#!/usr/bin/env python3
"""
NL2TLA+ Translation Script

Translates natural language descriptions of TLA+ specifications into TLA+ specifications.
This is a Python migration of the GenAI script translate.genai.mts using LiteLLM and MCP tools.

USAGE:
    python translate.py [puzzle_files...]
    
    # Test MCP connection
    python translate.py --test-mcp
    
    # Process specific puzzle files
    python translate.py DieHard.md CoffeeCan.md
    
    # Enable debug logging
    python translate.py --debug DieHard.md
    
    # Use different model
    python translate.py --model azure/gpt-4o DieHard.md
    
    # Use AWS Bedrock
    python translate.py --model bedrock/anthropic.claude-sonnet-4-20250514-v1:0 --model-id arn:aws:bedrock:us-east-1:024871859028:inference-profile/us.anthropic.claude-sonnet-4-20250514-v1:0 DieHard.md

REQUIREMENTS:
    - TLA+ MCP server running on http://localhost:59071/mcp
    - Java with tla2tools.jar available in current directory
    - API credentials for either Azure OpenAI or AWS Bedrock:
      
      Azure OpenAI:
      - AZURE_API_KEY
      - AZURE_API_BASE
      - AZURE_API_VERSION
      
      AWS Bedrock (option 1 - bearer token):
      - AWS_BEARER_TOKEN_BEDROCK
      
      AWS Bedrock (option 2 - standard AWS credentials):
      - AWS_ACCESS_KEY_ID
      - AWS_SECRET_ACCESS_KEY
      - AWS_REGION (optional)

PIPELINE:
    1. Synthesize TLA+ specification from natural language puzzle description
    2. Validate specification with TLC (expects counterexample, exit code 12)
    3. Copy gold standard specification from gold/ directory
    4. Synthesize trace refinement mapping from counterexample to gold standard
    5. Validate trace refinement with TLC
    6. Synthesize full refinement mapping from original spec to gold standard
    7. Validate full refinement with TLC

FILES GENERATED:
    For puzzle "DieHard.md":
    - DieHard.tla: Main TLA+ specification
    - DieHard.cfg: TLC configuration file
    - DieHardGold.tla: Gold standard specification (copied)
    - DieHardTrace.tla: Counterexample trace
    - DieHardTraceRef.tla: Trace refinement specification
    - DieHardTraceRef.cfg: Trace refinement configuration
    - DieHardRef.tla: Full refinement specification
    - DieHardRef.cfg: Full refinement configuration
"""

import asyncio
import json
import os
import sys
import subprocess
import shutil
import argparse
from pathlib import Path
from typing import List, Dict, Any, Callable, Optional
import logging

from litellm import acompletion
from litellm.proxy._experimental.mcp_server.mcp_server_manager import (
    MCPServerManager,
    MCPTransport,
)

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
    ]
)
logger = logging.getLogger(__name__)


class TLATranslator:
    """Main class for translating natural language to TLA+ specifications."""
    
    def __init__(self, model: str = "azure/gpt-4.1", model_id: Optional[str] = None, mcp_url: str = "http://localhost:59071/mcp"):
        self.model = model
        self.model_id = model_id
        self.mcp_url = mcp_url
        self.mcp_server_manager = None
        self.available_tools = []
        self.available_resources = []
        self.workspace_root = Path.cwd()
        
    async def setup_mcp_connection(self, max_retries: int = 3, timeout: float = 30.0):
        """Initialize MCP server connection and discover available tools with retry logic."""
        logger.info("🔌 Setting up MCP connection...")
        
        for attempt in range(max_retries):
            try:
                logger.debug(f"🔌 MCP connection attempt {attempt + 1}/{max_retries}")
                
                self.mcp_server_manager = MCPServerManager()
                
                config = {
                    "tlaplus_mcp_server": {
                        "url": self.mcp_url,
                        "transport": MCPTransport.http,
                    }
                }
                
                self.mcp_server_manager.load_servers_from_config(config)
                logger.info("✅ MCP server manager configured successfully!")
                
                # Discover available tools with timeout
                try:
                    self.available_tools = await asyncio.wait_for(
                        self.mcp_server_manager.list_tools(),
                        timeout=timeout
                    )
                    logger.info(f"🔧 Discovered {len(self.available_tools)} MCP tools")
                    for tool in self.available_tools:
                        logger.debug(f"  - {tool.name}: {tool.description}")
                    
                    # Test connection with a simple tool call
                    test_result = await self.call_mcp_tool("tlaplus_mcp_sany_modules", {}, max_retries=1, timeout=10.0)
                    if test_result.get("isError"):
                        raise RuntimeError(f"MCP test call failed: {test_result.get('error')}")
                    
                    # Discover available resources
                    try:
                        self.available_resources = await asyncio.wait_for(
                            self.list_mcp_resources(),
                            timeout=timeout
                        )
                        logger.info(f"📚 Discovered {len(self.available_resources)} MCP resources")
                        for resource in self.available_resources[:3]:  # Show first 3 resources
                            logger.debug(f"  - {resource.get('name', resource.get('uri', 'Unknown'))}: {resource.get('description', 'No description')}")
                        if len(self.available_resources) > 3:
                            logger.debug(f"  ... and {len(self.available_resources) - 3} more resources")
                    except Exception as e:
                        logger.warning(f"⚠️ Failed to discover MCP resources: {e}")
                        self.available_resources = []
                    
                    logger.info("✅ MCP connection established and tested successfully!")
                    return
                    
                except asyncio.TimeoutError:
                    logger.warning(f"⏰ MCP tool discovery timed out after {timeout}s (attempt {attempt + 1}/{max_retries})")
                    if attempt == max_retries - 1:
                        raise RuntimeError(f"MCP tool discovery timed out after {timeout}s")
                        
                except Exception as e:
                    logger.warning(f"⚠️ MCP tool discovery failed: {e} (attempt {attempt + 1}/{max_retries})")
                    if attempt == max_retries - 1:
                        raise RuntimeError(f"Failed to discover MCP tools: {e}")
                        
                # Wait before retry with exponential backoff
                if attempt < max_retries - 1:
                    wait_time = 2 ** attempt
                    logger.info(f"⏳ Waiting {wait_time}s before retry...")
                    await asyncio.sleep(wait_time)
                    
            except Exception as e:
                logger.error(f"❌ MCP connection setup failed: {e} (attempt {attempt + 1}/{max_retries})")
                if attempt == max_retries - 1:
                    raise RuntimeError(f"Failed to setup MCP connection after {max_retries} attempts: {e}")
                    
                # Wait before retry
                if attempt < max_retries - 1:
                    wait_time = 2 ** attempt
                    logger.info(f"⏳ Waiting {wait_time}s before retry...")
                    await asyncio.sleep(wait_time)
                    
    async def list_mcp_resources(self, max_retries: int = 3, timeout: float = 30.0) -> List[Dict[str, Any]]:
        """List all resources available across all MCP servers."""
        if not self.mcp_server_manager:
            logger.warning("⚠️ MCP server manager not initialized")
            return []
            
        resources = []
        
        try:
            # Get the registry of servers
            registry = self.mcp_server_manager.get_registry()
            
            for server_id, server in registry.items():
                logger.debug(f"🔍 Listing resources from server: {server.server_name}")
                
                try:
                    # Create MCP client for this server
                    client = self.mcp_server_manager._create_mcp_client(server)
                    
                    try:
                        # Connect to the server
                        await asyncio.wait_for(client.connect(), timeout=timeout)
                        
                        # Try to list resources using the MCP protocol
                        # This uses the resources/list method from the MCP specification
                        # The LiteLLM MCPClient doesn't expose list_resources directly,
                        # but the underlying session does
                        try:
                            if hasattr(client, '_session') and hasattr(client._session, 'list_resources'):
                                resources_result = await asyncio.wait_for(
                                    client._session.list_resources(),
                                    timeout=timeout
                                )
                            else:
                                logger.debug(f"⚠️ Client for {server.server_name} doesn't have session.list_resources")
                                continue
                            
                            if hasattr(resources_result, 'resources'):
                                server_resources = resources_result.resources
                            else:
                                server_resources = resources_result
                                
                            # Add server context to each resource
                            for resource in server_resources:
                                resource_info = {
                                    'server_name': server.server_name,
                                    'server_id': server_id,
                                    'uri': getattr(resource, 'uri', ''),
                                    'name': getattr(resource, 'name', ''),
                                    'description': getattr(resource, 'description', ''),
                                    'mimeType': getattr(resource, 'mimeType', ''),
                                }
                                resources.append(resource_info)
                                
                            logger.info(f"✅ Found {len(server_resources)} resources from {server.server_name}")
                            
                        except AttributeError:
                            # Server might not support list_resources method
                            logger.debug(f"⚠️ Server {server.server_name} does not support list_resources")
                        except Exception as e:
                            logger.debug(f"⚠️ Failed to list resources from {server.server_name}: {e}")
                            
                    finally:
                        try:
                            await client.disconnect()
                        except:
                            pass
                            
                except Exception as e:
                    logger.warning(f"⚠️ Failed to connect to server {server.server_name}: {e}")
                    continue
                    
        except Exception as e:
            logger.error(f"❌ Failed to list MCP resources: {e}")
            
        logger.info(f"📚 Discovered {len(resources)} total resources from all servers")
        return resources
        
    async def read_mcp_resource(self, resource_uri: str, server_name: str = None) -> Dict[str, Any]:
        """Read content from an MCP resource."""
        if not self.mcp_server_manager:
            logger.warning("⚠️ MCP server manager not initialized")
            return {"error": "MCP server manager not initialized", "isError": True}
            
        try:
            # Get the registry of servers
            registry = self.mcp_server_manager.get_registry()
            
            # Find the server that has this resource
            target_server = None
            if server_name:
                for server_id, server in registry.items():
                    if server.server_name == server_name:
                        target_server = server
                        break
            else:
                # If no server specified, try the first server
                if registry:
                    target_server = next(iter(registry.values()))
            
            if not target_server:
                return {"error": f"Server {server_name} not found", "isError": True}
                
            try:
                # Create MCP client for this server
                client = self.mcp_server_manager._create_mcp_client(target_server)
                
                try:
                    # Connect to the server
                    await client.connect()
                    
                    # Read the resource using the underlying session
                    if hasattr(client, '_session') and hasattr(client._session, 'read_resource'):
                        resource_result = await client._session.read_resource(resource_uri)
                    else:
                        return {"error": f"Client doesn't support read_resource", "isError": True}
                    
                    # Extract content from the result
                    if hasattr(resource_result, 'contents'):
                        contents = resource_result.contents
                        if contents and len(contents) > 0:
                            content = contents[0]
                            return {
                                "content": getattr(content, 'text', str(content)),
                                "mimeType": getattr(content, 'mimeType', 'text/plain'),
                                "isError": False
                            }
                    
                    return {"content": str(resource_result), "isError": False}
                    
                finally:
                    try:
                        await client.disconnect()
                    except:
                        pass
                        
            except Exception as e:
                logger.error(f"❌ Failed to read resource {resource_uri}: {e}")
                return {"error": str(e), "isError": True}
                
        except Exception as e:
            logger.error(f"❌ Failed to read MCP resource: {e}")
            return {"error": str(e), "isError": True}
            
    async def gpt_call(self, messages: List[Dict[str, str]]) -> str:
        """Make a call to the LLM."""
        try:
            # Validate messages to prevent empty content that causes Bedrock API errors
            validated_messages = []
            for msg in messages:
                content = msg.get("content", "").strip()
                if not content:
                    logger.warning(f"⚠️ Skipping empty message with role: {msg.get('role', 'unknown')}")
                    continue
                validated_messages.append({
                    "role": msg["role"],
                    "content": content
                })
            
            if not validated_messages:
                raise ValueError("No valid messages to send to LLM")
            
            # Prepare completion parameters
            completion_params = {
                "model": self.model,
                "messages": validated_messages,
                "stream": False,
            }
            
            # Add model_id if specified (required for AWS Bedrock)
            if self.model_id:
                completion_params["model_id"] = self.model_id
            
            response = await acompletion(**completion_params)
            return response["choices"][0]["message"]["content"]
        except Exception as e:
            logger.error(f"❌ LLM call failed: {e}")
            raise
            
    async def call_mcp_tool(self, tool_name: str, params: Dict[str, Any], max_retries: int = 3, timeout: float = 60.0) -> Dict[str, Any]:
        """Call an MCP tool and return the result with retry logic and timeout handling."""
        for attempt in range(max_retries):
            try:
                logger.debug(f"🔧 Calling MCP tool: {tool_name} with {params} (attempt {attempt + 1}/{max_retries})")
                
                # Use asyncio.wait_for to add timeout protection
                tool_result = await asyncio.wait_for(
                    self.mcp_server_manager.call_tool(name=tool_name, arguments=params),
                    timeout=timeout
                )
                
                # Extract the content from the CallToolResult object
                if hasattr(tool_result, "content") and tool_result.content:
                    tool_response = {
                        "content": [
                            {"type": item.type, "text": item.text}
                            for item in tool_result.content
                        ],
                        "isError": getattr(tool_result, "isError", False),
                    }
                else:
                    tool_response = {"content": str(tool_result), "isError": False}
                    
                logger.debug(f"✅ MCP tool {tool_name} completed successfully")
                return tool_response
                
            except asyncio.TimeoutError:
                logger.warning(f"⏰ MCP tool {tool_name} timed out after {timeout}s (attempt {attempt + 1}/{max_retries})")
                if attempt == max_retries - 1:
                    return {"error": f"Tool {tool_name} timed out after {timeout}s", "isError": True}
                await asyncio.sleep(2 ** attempt)  # Exponential backoff
                
            except asyncio.CancelledError:
                logger.warning(f"🚫 MCP tool {tool_name} was cancelled (attempt {attempt + 1}/{max_retries})")
                if attempt == max_retries - 1:
                    return {"error": f"Tool {tool_name} was cancelled", "isError": True}
                await asyncio.sleep(2 ** attempt)  # Exponential backoff
                
            except Exception as e:
                logger.error(f"❌ MCP tool {tool_name} failed with error: {e} (attempt {attempt + 1}/{max_retries})")
                if attempt == max_retries - 1:
                    return {"error": str(e), "isError": True}
                await asyncio.sleep(2 ** attempt)  # Exponential backoff
                
        return {"error": f"Tool {tool_name} failed after {max_retries} attempts", "isError": True}
            
    def run_tlc_and_validate(
        self, 
        tla_file: str, 
        cfg_file: str, 
        check_name: str, 
        validate_exit_code: Callable[[int], bool],
        extra_args: List[str] = None
    ) -> subprocess.CompletedProcess:
        """Run TLC and validate exit code with custom validation."""
        if extra_args is None:
            extra_args = []
            
        args = [
            'java', '-XX:+UseParallelGC', '-jar', 'tla2tools.jar', 
            tla_file, '-config', cfg_file, '-note', '-cleanup'
        ] + extra_args
        
        logger.info(f"🔍 Running TLC for {check_name}: {' '.join(args)}")
        
        try:
            result = subprocess.run(args, capture_output=True, text=True, cwd=self.workspace_root)
            
            if not validate_exit_code(result.returncode):
                logger.error(f"TLC exited with code {result.returncode}")
                logger.error(f"Output: {result.stdout}")
                logger.error(f"Error: {result.stderr}")
                raise RuntimeError(f"{check_name} did not exit with expected exit code. Check the output for details.")
                
            logger.info(f"✅ {check_name} completed successfully (exit code: {result.returncode})")
            return result
            
        except subprocess.SubprocessError as e:
            logger.error(f"❌ Failed to run TLC: {e}")
            raise
            
    async def create_tools_description(self) -> str:
        """Create a comprehensive description of available MCP tools and resources for the LLM."""
        tool_descriptions = []
        
        for tool in self.available_tools:
            tool_name = tool.name
            tool_desc = tool.description
            
            # Extract comprehensive parameter info from input schema
            params_section = ""
            if hasattr(tool, 'inputSchema') and tool.inputSchema:
                schema = tool.inputSchema
                if 'properties' in schema:
                    required_params = schema.get('required', [])
                    param_details = []
                    
                    for param_name, param_info in schema['properties'].items():
                        param_type = param_info.get('type', 'string')
                        param_desc = param_info.get('description', 'No description available')
                        is_required = param_name in required_params
                        
                        # Handle enum values
                        enum_info = ""
                        if 'enum' in param_info:
                            enum_values = param_info['enum']
                            enum_info = f" (options: {', '.join(map(str, enum_values))})"
                        
                        # Handle array items
                        items_info = ""
                        if param_type == 'array' and 'items' in param_info:
                            items_type = param_info['items'].get('type', 'any')
                            items_info = f" of {items_type}"
                        
                        # Handle default values
                        default_info = ""
                        if 'default' in param_info:
                            default_info = f" (default: {param_info['default']})"
                        
                        # Handle minimum/maximum constraints
                        constraints_info = ""
                        if 'minimum' in param_info:
                            constraints_info += f" (min: {param_info['minimum']})"
                        if 'maximum' in param_info:
                            constraints_info += f" (max: {param_info['maximum']})"
                        
                        required_marker = " [REQUIRED]" if is_required else " [OPTIONAL]"
                        
                        param_details.append(
                            f"    - {param_name}: {param_type}{items_info}{enum_info}{default_info}{constraints_info}{required_marker}\n"
                            f"      {param_desc}"
                        )
                    
                    if param_details:
                        params_section = f"\n  Parameters:\n" + "\n".join(param_details)
            
            tool_example = f"- **{tool_name}**: {tool_desc}"
            if params_section:
                tool_descriptions.append(f"{tool_example}{params_section}")
            else:
                tool_descriptions.append(f"{tool_example}\n  No parameters required.")
        
        # Add resources section
        resources_section = ""
        if self.available_resources:
            resource_descriptions = []
            resource_descriptions.append("## Available MCP Resources")
            resource_descriptions.append("")
            resource_descriptions.append("The following resources are available for reading contextual information:")
            resource_descriptions.append("")
            
            for resource in self.available_resources:
                resource_desc = resource.get('description', 'No description available')
                resource_uri = resource.get('uri', '')
                resource_info = f"- {resource_uri}"
                resource_info += f": {resource_desc}"
                
                resource_descriptions.append(resource_info)
            
            resources_section = "\n".join(resource_descriptions)
        
        # Combine tools and resources
        full_description = "\n\n".join(tool_descriptions)
        if resources_section:
            full_description += "\n\n" + resources_section
            
        return full_description
        
    async def run_agent_prompt(self, user_prompt: str, max_turns: int = 15) -> str:
        """Run an agent-based prompt with MCP tool access using ReAct pattern."""
        tools_description = await self.create_tools_description()
        
        system_prompt = f"""You are an autonomous AI agent that can use MCP tools to accomplish TLA+ development tasks.

CRITICAL: You MUST respond with ONLY valid JSON. No explanations, no markdown, no additional text.

## Available MCP Tools and Resources

{tools_description}

### Response Format (JSON only)

To call a tool:
{{"action": "call_tool", "tool": "<tool_name>", "params": {{"param1": "value1", "param2": "value2"}}}}

To read a resource:
{{"action": "read_resource", "uri": "<resource_uri>"}}

### Important Tool Usage Guidelines

- **Valid actions**: Use only the actions listed above (call_tool and read_resource). Do not invent your own actions.
- **One action per request**: Use only one action per request. You cannot invoke multiple actions in a single request.
- **File Paths**: Use absolute file paths when required by tools. Current working directory: {self.workspace_root}
- **Parameter Requirements**: Pay attention to [REQUIRED] vs [OPTIONAL] parameter markers above
- **Parameter Types**: Ensure parameter values match the expected types (string, number, boolean, array)

## Important TLA+ Usage Guidelines

- **Divide and conquer**: If necessary, break down the problem into smaller sub-problems and solve them one by one.
- **TLA+ Validation**: Always validate your TLA+ specifications by parsing them with SANY
- **Configuration Files**: Generate appropriate TLC configuration files for model checking
- **Error Handling**: Fix any syntax or configuration errors that arise based on tool feedback
- **Best Practices**: Follow TLA+ best practices and conventions
- **Reuse existing modules**: Try to reuse existing operators and modules from the TLA+ standard and Community Modules.
"""

        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ]
        
        final_result = ""
        
        for turn in range(max_turns):
            logger.info(f"🤖 Agent turn {turn + 1}/{max_turns}")
            
            # Get LLM response
            content = await self.gpt_call(messages)
            logger.debug(f"LLM Response: {content}")
            
            try:
                # Strip markdown code blocks if present
                cleaned_content = content.strip()
                if cleaned_content.startswith("```json"):
                    cleaned_content = cleaned_content[7:]  # Remove ```json
                if cleaned_content.startswith("```"):
                    cleaned_content = cleaned_content[3:]   # Remove ```
                if cleaned_content.endswith("```"):
                    cleaned_content = cleaned_content[:-3]  # Remove trailing ```
                cleaned_content = cleaned_content.strip()
                
                action = json.loads(cleaned_content)
            except json.JSONDecodeError as e:
                logger.warning(f"⚠️ LLM did not return valid JSON: {e}")
                logger.debug(f"Raw content: {content}")
                # Try to continue with a clarification
                messages.append({"role": "assistant", "content": content})
                messages.append({
                    "role": "system", 
                    "content": "One action per request. Please respond with valid JSON only. Use either {\"action\": \"call_tool\", \"tool\": \"<tool_name>\", \"params\": {...}} or {\"action\": \"read_resource\", \"uri\": \"<resource_uri>\"}"
                })
                continue
                
            if action.get("action") == "call_tool":
                tool = action["tool"]
                params = action.get("params", {})
                
                logger.info(f"🔧 Calling MCP tool: {tool} with {params}")
                tool_response = await self.call_mcp_tool(tool, params)
                
                messages.append({"role": "assistant", "content": content})
                
                # Handle tool errors more gracefully
                if tool_response.get("isError"):
                    logger.warning(f"⚠️ Tool {tool} returned error: {tool_response}")
                    error_msg = tool_response.get("error", "Unknown error")
                    messages.append({
                        "role": "system",
                        "content": f"Tool Error: {tool} failed with error: {error_msg}. Please try a different approach or fix the issue."
                    })
                else:
                    logger.info(f"✅ Tool {tool} completed successfully")
                    messages.append({
                        "role": "system",
                        "content": f"Observation: {json.dumps(tool_response)}"
                    })
                    
            elif action.get("action") == "read_resource":
                resource_uri = action.get("uri", "")
                server_name = action.get("server", "")
                
                logger.info(f"📚 Reading MCP resource: {resource_uri} from {server_name}")
                resource_response = await self.read_mcp_resource(resource_uri, server_name)
                
                messages.append({"role": "assistant", "content": content})
                
                # Handle resource read errors more gracefully
                if resource_response.get("isError"):
                    logger.warning(f"⚠️ Resource read failed: {resource_response}")
                    error_msg = resource_response.get("error", "Unknown error")
                    messages.append({
                        "role": "system",
                        "content": f"Resource Error: Failed to read {resource_uri}: {error_msg}. Please try a different resource or approach."
                    })
                else:
                    logger.info(f"✅ Resource {resource_uri} read successfully")
                    resource_content = resource_response.get("content", "")
                    mime_type = resource_response.get("mimeType", "text/plain")
                    messages.append({
                        "role": "system",
                        "content": f"Resource Content ({mime_type}): {resource_content}"
                    })
                    
            else:
                logger.warning(f"⚠️ Unknown action type: {action.get('action')}")
                messages.append({"role": "assistant", "content": content})
                messages.append({
                    "role": "system",
                    "content": "Unknown action. Please use 'call_tool' or 'read_resource'."
                })
                
        return final_result or "Agent completed without explicit final answer"
        
    async def synthesize_tla_specification(self, puzzle_file: Path, tla_file: str, cfg_file: str) -> str:
        """Synthesize TLA+ specification from puzzle description."""
        logger.info(f"🔨 Synthesizing TLA+ specification for {puzzle_file}")
        
        # Read the puzzle file
        puzzle_content = puzzle_file.read_text()
        
        prompt = f"""Create a TLA+ specification in a new file {tla_file} that formalizes the problem described below, including all relevant requirements and constraints.

Problem Description:
{puzzle_content}

Steps to complete:
1. Write the TLA+ specification to file {tla_file}
2. Parse the specification using SANY via the **tlaplus_mcp_sany_parse** tool
3. If parsing fails, revise the specification until it parses successfully
4. Generate a TLC configuration file {cfg_file} 
5. Use the **tlaplus_mcp_sany_symbol** tool to identify relevant symbols needed in the config file
6. Verify the specification using the TLC model checker via the **tlaplus_mcp_tlc_check** tool
7. Determine whether the expected counterexample is found

Do not ignore tool warnings or errors - correct them based on the feedback provided by the tools. Consult the TLA+ knowledge base when writing the specification."""

        result = await self.run_agent_prompt(prompt)
        return result
        
    async def synthesize_trace_refinement(
        self, 
        tla_file: str, 
        gold_file: str, 
        trace_file: str, 
        trace_ref_file: str, 
        trace_cfg_file: str
    ) -> str:
        """Synthesize trace refinement mapping to gold standard."""
        logger.info(f"🔨 Synthesizing trace refinement from {tla_file} to {gold_file}")
        
        prompt = f"""Use the TLC model checker to create a trace refinement mapping.

Steps to complete:
1. Use the **tlaplus_mcp_tlc_check** tool with the **-dumptrace tlcTESpec {trace_file}** option to serialize a counterexample trace to file {trace_file} for the TLA+ specification {tla_file}
2. Create a refinement mapping from {trace_file} to the gold-standard specification {gold_file} in a new spec {trace_ref_file} that extends {trace_file} and refines {gold_file}
3. You must not modify {trace_file} or {gold_file} specification directly
4. Parse the refinement using the **tlaplus_mcp_sany_parse** tool
5. If parsing fails, revise the refinement until it is valid
6. Once the refinement is correctly parsed, use the **tlaplus_mcp_tlc_check** tool to verify whether the refinement holds
7. Use the **tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the {trace_cfg_file} config file

Consult the TLA+ knowledge base when refining the specification."""

        result = await self.run_agent_prompt(prompt)
        return result
        
    async def synthesize_full_refinement(
        self, 
        tla_file: str, 
        gold_file: str, 
        ref_tla_file: str, 
        ref_cfg_file: str
    ) -> str:
        """Synthesize full refinement mapping to gold standard."""
        logger.info(f"🔨 Synthesizing full refinement from {tla_file} to {gold_file}")
        
        prompt = f"""Define a refinement mapping from the specification {tla_file} to the specification {gold_file}.

Steps to complete:
1. You must not modify either specification directly
2. Instead, create a new TLA+ module {ref_tla_file} that extends {tla_file} and instantiates {gold_file}
3. Parse the refinement module using the **tlaplus_mcp_sany_parse** tool
4. If parsing fails, revise the module until it is valid
5. Use the **tlaplus_mcp_tlc_check** tool to check whether the refinement mapping holds
6. Use the **tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the {ref_cfg_file} config file

Consult the TLA+ knowledge base when refining the specification."""

        result = await self.run_agent_prompt(prompt)
        return result
        
    async def process_puzzle_file(self, puzzle_file: Path):
        """Process a single puzzle file through the complete TLA+ translation pipeline."""
        logger.info(f"🎯 Processing puzzle file: {puzzle_file}")
        
        # Extract file names
        base_name = puzzle_file.stem  # filename without extension
        tla_file = f"{base_name}.tla"
        cfg_file = f"{base_name}.cfg"
        
        phase_results = {}
        
        try:
            # Phase 1: Synthesize TLA+ specification
            logger.info("📝 Phase 1: Synthesizing TLA+ specification")
            try:
                synthesis_result = await self.synthesize_tla_specification(puzzle_file, tla_file, cfg_file)
                phase_results["synthesis"] = synthesis_result
                logger.info(f"✅ Created TLA+ specification: {tla_file}")
            except Exception as e:
                logger.error(f"❌ Phase 1 failed: {e}")
                raise RuntimeError(f"Failed to synthesize TLA+ specification: {e}") from e
            
            # Phase 2: Validate TLA+ specification
            logger.info("🔍 Phase 2: Validating TLA+ specification")
            try:
                # Exit code 12 indicates TLC found a counterexample (expected for puzzles)
                self.run_tlc_and_validate(tla_file, cfg_file, "Synthesized spec validation", lambda code: code == 12)
                phase_results["validation"] = "success"
            except Exception as e:
                logger.error(f"❌ Phase 2 failed: {e}")
                # Try to continue if files exist but validation failed
                if not (Path(tla_file).exists() and Path(cfg_file).exists()):
                    raise RuntimeError(f"TLA+ specification validation failed and files missing: {e}") from e
                logger.warning("⚠️ Continuing despite validation failure")
                phase_results["validation"] = f"failed: {e}"
            
            # Phase 3: Copy gold standard and synthesize trace refinement
            logger.info("🏆 Phase 3: Synthesizing trace refinement with gold standard")
            gold_file_module = f"{base_name}Gold"
            gold_file = f"{gold_file_module}.tla"
            gold_source = self.workspace_root / "gold" / f"{base_name}Gold.tla"
            
            if not gold_source.exists():
                logger.warning(f"⚠️ Gold standard file not found: {gold_source}")
                logger.info("🔄 Skipping refinement phases due to missing gold standard")
                return phase_results
                
            try:
                shutil.copy2(gold_source, self.workspace_root / gold_file)
                logger.info(f"📋 Copied gold standard: {gold_file}")
                
                trace_file = f"{base_name}Trace.tla"
                trace_ref_file = f"{base_name}TraceRef.tla"
                trace_cfg_file = f"{base_name}TraceRef.cfg"
                
                trace_result = await self.synthesize_trace_refinement(
                    tla_file, gold_file, trace_file, trace_ref_file, trace_cfg_file
                )
                phase_results["trace_refinement"] = trace_result
                logger.info(f"✅ Created TLA+ trace refinement: {trace_ref_file}")
            except Exception as e:
                logger.error(f"❌ Phase 3 failed: {e}")
                logger.warning("⚠️ Continuing to full refinement despite trace refinement failure")
                phase_results["trace_refinement"] = f"failed: {e}"
                # Set default file names for phase 4 validation
                trace_ref_file = f"{base_name}TraceRef.tla"
                trace_cfg_file = f"{base_name}TraceRef.cfg"
            
            # Phase 4: Validate trace refinement (only if files exist)
            if Path(trace_ref_file).exists() and Path(trace_cfg_file).exists():
                logger.info("🔍 Phase 4: Validating trace refinement")
                try:
                    self.run_tlc_and_validate(trace_ref_file, trace_cfg_file, "Trace refinement validation", lambda code: code == 0)
                    self.run_tlc_and_validate(
                        trace_ref_file, trace_cfg_file, 
                        "Trace refinement validation with refinement postcondition", 
                        lambda code: code == 0, 
                        ['-postcondition', f'{gold_file_module}!Refinement']
                    )
                    self.run_tlc_and_validate(
                        trace_ref_file, trace_cfg_file,
                        "Trace refinement validation with stats postcondition",
                        lambda code: code == 0,
                        ['-postcondition', f'{gold_file_module}!Stats']
                    )
                    phase_results["trace_validation"] = "success"
                except Exception as e:
                    logger.error(f"❌ Phase 4 failed: {e}")
                    logger.warning("⚠️ Continuing to full refinement despite trace validation failure")
                    phase_results["trace_validation"] = f"failed: {e}"
            else:
                logger.warning("⚠️ Skipping Phase 4: Trace refinement files not found")
                phase_results["trace_validation"] = "skipped: files not found"
            
            # Phase 5: Synthesize full refinement
            logger.info("🔗 Phase 5: Synthesizing full refinement")
            ref_tla_file = f"{base_name}Ref.tla"
            ref_cfg_file = f"{base_name}Ref.cfg"
            
            try:
                full_result = await self.synthesize_full_refinement(
                    tla_file, gold_file, ref_tla_file, ref_cfg_file
                )
                phase_results["full_refinement"] = full_result
                logger.info(f"✅ Created TLA+ full refinement: {ref_tla_file}")
            except Exception as e:
                logger.error(f"❌ Phase 5 failed: {e}")
                logger.warning("⚠️ Continuing to validation despite full refinement failure")
                phase_results["full_refinement"] = f"failed: {e}"
            
            # Phase 6: Validate full refinement (only if files exist)
            if Path(ref_tla_file).exists() and Path(ref_cfg_file).exists():
                logger.info("🔍 Phase 6: Validating full refinement")
                try:
                    self.run_tlc_and_validate(ref_tla_file, ref_cfg_file, "Full refinement validation", lambda code: code == 0)
                    self.run_tlc_and_validate(
                        ref_tla_file, ref_cfg_file,
                        "Full refinement validation with refinement postcondition",
                        lambda code: code == 0,
                        ['-postcondition', f'{gold_file_module}!Refinement']
                    )
                    self.run_tlc_and_validate(
                        ref_tla_file, ref_cfg_file,
                        "Full refinement validation with stats postcondition", 
                        lambda code: code == 0,
                        ['-postcondition', f'{gold_file_module}!Stats']
                    )
                    phase_results["full_validation"] = "success"
                except Exception as e:
                    logger.error(f"❌ Phase 6 failed: {e}")
                    phase_results["full_validation"] = f"failed: {e}"
            else:
                logger.warning("⚠️ Skipping Phase 6: Full refinement files not found")
                phase_results["full_validation"] = "skipped: files not found"
            
            # Summary
            successful_phases = sum(1 for result in phase_results.values() if result == "success" or (isinstance(result, str) and not result.startswith("failed:")))
            total_phases = len(phase_results)
            
            logger.info(f"🎉 Completed processing {puzzle_file} ({successful_phases}/{total_phases} phases successful)")
            
            return phase_results
            
        except Exception as e:
            logger.error(f"❌ Critical failure processing {puzzle_file}: {e}")
            # Log partial results for debugging
            if phase_results:
                logger.info(f"📊 Partial results: {phase_results}")
            raise
            
    async def run(self, puzzle_files: List[str]):
        """Run the complete TLA+ translation pipeline."""
        logger.info("🚀 Starting TLA+ translation pipeline")
        
        # Verify TLC installation
        logger.info("🔧 Verifying TLC installation")
        try:
            result = subprocess.run(
                ['java', '-XX:+UseParallelGC', '-jar', 'tla2tools.jar'], 
                capture_output=True, text=True, cwd=self.workspace_root
            )
            if result.returncode != 1:  # TLC should exit with code 1 when run without arguments
                logger.error(f"TLC exited with unexpected code {result.returncode}")
                logger.error(f"Output: {result.stdout}")
                raise RuntimeError("TLC installation missing or invalid")
        except subprocess.SubprocessError as e:
            logger.error(f"❌ Failed to verify TLC installation: {e}")
            raise
            
        logger.info("✅ TLC installation verified")
        
        # Setup MCP connection
        await self.setup_mcp_connection()
        
        # Process each puzzle file
        for puzzle_file_str in puzzle_files:
            puzzle_file = Path(puzzle_file_str)
            if not puzzle_file.exists():
                # Try relative to puzzles directory
                puzzle_file = self.workspace_root / "puzzles" / puzzle_file_str
                if not puzzle_file.exists():
                    logger.error(f"❌ Puzzle file not found: {puzzle_file_str}")
                    continue
                    
            await self.process_puzzle_file(puzzle_file)
            
        logger.info("🎉 TLA+ translation pipeline completed successfully")


def setup_environment():
    """Setup environment variables for Azure OpenAI and AWS Bedrock."""
    # Check for Azure OpenAI credentials
    if os.environ.get("AZURE_API_KEY"):
        logger.info(f"🔑 Using Azure API Base: {os.environ.get('AZURE_API_BASE')}")
        logger.info(f"🔑 Using Azure API Version: {os.environ.get('AZURE_API_VERSION')}")
    
    # Check for AWS Bedrock credentials
    elif os.environ.get("AWS_BEARER_TOKEN_BEDROCK"):
        logger.info("🔑 Using AWS Bedrock authentication")
    
    # Check for standard AWS credentials
    elif os.environ.get("AWS_ACCESS_KEY_ID") and os.environ.get("AWS_SECRET_ACCESS_KEY"):
        logger.info("🔑 Using AWS credentials for Bedrock")
        if os.environ.get("AWS_REGION"):
            logger.info(f"🔑 AWS Region: {os.environ.get('AWS_REGION')}")
    
    else:
        logger.warning("⚠️ No API credentials found. Please set either:")
        logger.warning("   - AZURE_API_KEY for Azure OpenAI")
        logger.warning("   - AWS_BEARER_TOKEN_BEDROCK for AWS Bedrock with bearer token")
        logger.warning("   - AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY for AWS Bedrock")


async def test_mcp_connection(mcp_url: str = "http://localhost:59071/mcp"):
    """Test MCP connection independently."""
    logger.info("🔌 Testing MCP connection...")
    
    try:
        mcp_server_manager = MCPServerManager()
        config = {
            "tlaplus_mcp_server": {
                "url": mcp_url,
                "transport": MCPTransport.http,
            }
        }
        mcp_server_manager.load_servers_from_config(config)
        logger.info("✅ MCP server manager configured successfully!")
        
        # List available tools
        tools_result = await mcp_server_manager.list_tools()
        logger.info(f"🔧 Available tools ({len(tools_result)}):")
        for tool in tools_result[:5]:  # Show first 5 tools
            logger.info(f"  - {tool.name}: {tool.description}")
        if len(tools_result) > 5:
            logger.info(f"  ... and {len(tools_result) - 5} more tools")
            
        # Test calling a simple tool
        try:
            tool_response = await mcp_server_manager.call_tool(
                name="tlaplus_mcp_sany_modules", arguments={}
            )
            logger.info(f"🎯 Test tool call successful: {type(tool_response)}")
            
            # Test resource listing
            try:
                translator = TLATranslator(mcp_url=mcp_url)
                translator.mcp_server_manager = mcp_server_manager
                resources = await translator.list_mcp_resources()
                logger.info(f"📚 Test resource listing successful: found {len(resources)} resources")
                for resource in resources[:3]:  # Show first 3
                    logger.info(f"  - {resource.get('name', resource.get('uri', 'Unknown'))}")
            except Exception as e:
                logger.warning(f"⚠️ Test resource listing failed: {e}")
            
            return True
        except Exception as e:
            logger.warning(f"⚠️ Test tool call failed: {e}")
            return False
            
    except Exception as e:
        logger.error(f"❌ MCP connection test failed: {e}")
        return False


async def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Translate natural language to TLA+ specifications")
    parser.add_argument(
        "puzzle_files", 
        nargs="*", 
        default=["DieHard.md"],
        help="Puzzle files to process (default: DieHard.md)"
    )
    parser.add_argument(
        "--model", 
        default="azure/gpt-4.1",
        help="LLM model to use (default: azure/gpt-4.1). For Bedrock use format: bedrock/anthropic.claude-sonnet-4-20250514-v1:0"
    )
    parser.add_argument(
        "--model-id", 
        help="Model ID for AWS Bedrock (e.g., arn:aws:bedrock:us-east-1:024871859028:inference-profile/us.anthropic.claude-sonnet-4-20250514-v1:0)"
    )
    parser.add_argument(
        "--mcp-url", 
        default="http://localhost:59071/mcp",
        help="MCP server URL (default: http://localhost:59071/mcp)"
    )
    parser.add_argument(
        "--debug", 
        action="store_true",
        help="Enable debug logging"
    )
    parser.add_argument(
        "--test-mcp", 
        action="store_true",
        help="Test MCP connection only and exit"
    )
    
    args = parser.parse_args()
    
    if args.debug:
        logging.getLogger().setLevel(logging.DEBUG)
        
    setup_environment()
    
    # Test MCP connection if requested
    if args.test_mcp:
        success = await test_mcp_connection(args.mcp_url)
        sys.exit(0 if success else 1)
    
    translator = TLATranslator(model=args.model, model_id=getattr(args, 'model_id', None), mcp_url=args.mcp_url)
    
    try:
        await translator.run(args.puzzle_files)
    except KeyboardInterrupt:
        logger.info("🛑 Translation interrupted by user")
    except Exception as e:
        logger.error(f"❌ Translation failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())

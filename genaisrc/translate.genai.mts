script({
    title: "NL2TLA+ translation",
    description: "Translate a natural language description of a TLA+ specification into a TLA+ specification.",
    files: ["puzzles/DieHard.md"],
    systemSafety: false,
    system: [
        "system.fs_read_file",
        //     "system.files",
        //     "system.fs_find_files",
        //     "system.do_not_explain",
        //     "system.tool_calls",
        //     "system.tools"
    ],
    // fallbackTools: false,
    // model: "github:openai/o3-mini"
    temperature: 0,
    // https://microsoft.github.io/genaiscript/reference/scripts/inline-prompts/#inline-only-scripts
    model: "none",
    // https://microsoft.github.io/genaiscript/reference/scripts/inline-prompts/#concurrency
    modelConcurrency: { "github_copilot_chat:current": 1 }
})
// defTool({
//     tla: {
//         url: "http://localhost:59071/mcp",
//         type: "http"
//     }
// })
// defTool(
//     "fs_write_file",
//     "Writes text to a file in the file system. Use this to create or update files before using the TLA+ MCP tools.",
//     {
//         filename: { type: "string" },
//         content: { type: "string" },
//     },
//     async ({ filename, content }) => {
//         await workspace.writeText(filename, content);
//         return { success: true, filename };
//     }
// )

// Helper function to set up common tools for TLA+ contexts
function setupTLATools(ctx) {
    // The TLA+ MCP tools have to be started separately.
    ctx.defTool({
        tla: {
            url: "http://localhost:59071/mcp",
            type: "http"
        }
    });
    // See https://github.com/microsoft/genaiscript/issues/1809 why we define fs_write_file.
    ctx.defTool(
        "fs_write_file",
        "Writes text to a file in the file system. Use this to create or update files before using the TLA+ MCP tools.",
        {
            filename: { type: "string" },
            content: { type: "string" },
        },
        async ({ filename, content }) => {
            await workspace.writeText(filename, content);
            return { success: true, filename };
        }
    );
}

// ----------------- //
const { dbg } = env

// Iterate over each file provided by the environment
for (const file of env.files) {

    // -------- Synthesize TLA+ specification -------- //

    if (!file) cancel("no puzzle file provided");

    const baseName = file.filename.replace(/\.[^.]*$/, '');
    const fileName = baseName.split('/').pop();
    const tlaFile = fileName + ".tla";
    const cfgFile = fileName + ".cfg";

    const synthesize = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Create a TLA+ specification in a new file ${tlaFile} that formalizes the problem described in ${file.filename}, including all relevant requirements and constraints. Use the **fs_write_file tool** to write the specification. Then, parse the specification using the TLC model checker via the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the specification until it parses successfully. Next, generate a TLC configuration file ${cfgFile}. Use the **tla_tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the config file. Finally, verify the specification using the TLC model checker via the **tla_tlaplus_mcp_tlc_check** tool and determine whether the expected counterexample is found.`
        },
        { model: "github_copilot_chat:current", system: ["system.fs_read_file"] });
    dbg(synthesize);
    console.log(`Created TLA+ specification: ${synthesize}`);

    // Copy the gold standard solution file from the gold/ directory to the workspace root.
    const goldFile = `gold/${fileName}Gold.tla`;
    await workspace.copyFile(goldFile, `${fileName}Gold.tla`)

    // -------- Verify refinement of counterexample with gold standard spec -------- //

    const traceFile = `${fileName}_TTrace_123456789.tla`;
    const traceRefinement = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Use the TLC model checker via the **tla_tlaplus_mcp_tlc_check** tool with the **-generateSpecTE** option to serialize a counterexample trace for the TLA+ specification ${tlaFile}. Save this trace to a file named ${traceFile}, where 123456789 represents a timestamp. Next, create a refinement mapping from ${traceFile} to the gold-standard specification ${goldFile}. Parse the refinement using the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the refinement until it is valid. Once the refinement is correctly parsed, use the **tla_tlaplus_mcp_tlc_check** tool to verify whether the refinement holds.`
        },
        { model: "github_copilot_chat:current", system: ["system.fs_read_file", "system.fs_find_files"] });
    dbg(traceRefinement);
    console.log(`Created TLA+ trace refinement: ${traceRefinement}`);

    // -------- Verify full refinement of gold standard spec -------- //
    
    const refTLAFile = `${fileName}Ref.tla`;
    const fullRefinement = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Define a refinement mapping from the specification ${tlaFile} to the specification ${fileName}Gold.tla. You must not modify either specification directly. Instead, create a new TLA+ module ${refTLAFile} that extends ${tlaFile} and instantiates ${goldFile}. Parse the refinement module using the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the module until it is valid. Finally, use the **tla_tlaplus_mcp_tlc_check** tool to check whether the refinement mapping holds.`
        },
        { model: "github_copilot_chat:current", system: ["system.fs_read_file"] });
    dbg(fullRefinement);
    console.log(`Created TLA+ full refinement: ${fullRefinement}`);
}

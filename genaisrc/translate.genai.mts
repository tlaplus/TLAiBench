script({
    title: "NL2TLA+ translation",
    description: "Translate a natural language description of a TLA+ specification into a TLA+ specification.",
    files: ["puzzles/DieHard.md"],
    systemSafety: false,
    temperature: 0,
    // https://microsoft.github.io/genaiscript/reference/scripts/inline-prompts/#inline-only-scripts
    model: "none",  // "github:openai/o3-mini"
    // https://microsoft.github.io/genaiscript/reference/scripts/inline-prompts/#concurrency
    modelConcurrency: { "github_copilot_chat:current": 1 }
})

// https://microsoft.github.io/genaiscript/reference/scripts/tools/#reusing-tools-in-system-scripts
function setupTLATools(ctx: ChatGenerationContext) {
    // The TLA+ MCP tools have to be started separately.
    ctx.defTool({
        tla: {
            url: "http://localhost:59071/mcp",
            type: "http"
        }
    });
}

// ----------------- //
const { dbg } = env

// Assert that TLC can be run locally
const shellOutput = await host.exec(`java`, ['-jar', 'tla2tools.jar']);
if (shellOutput.exitCode !== 1) {
    console.error(`TLC exited with code ${shellOutput.exitCode}. Output: ${shellOutput.stdout}`);
    cancel(`TLC installation missing. TLC did not exit with expected exit code. Check the output for details.`);
}

// Iterate over each file provided by the environment
for (const file of env.files) {

    // -------- Synthesize TLA+ specification -------- //

    if (!file) cancel("no puzzle file provided");

    const baseName = file.filename.replace(/\.[^.]*$/, '');
    const fileName = baseName.split('/').pop();
    const tlaFile = fileName + ".tla";
    const cfgFile = fileName + ".cfg";

    // TODO Import the TLA+ rules with: https://microsoft.github.io/genaiscript/reference/scripts/import-template/
    // Fetch TLC's explain files could be done with: https://microsoft.github.io/genaiscript/reference/scripts/fetch/
    // Alternatively, GenAIScript's vector search could be used to find the relevant rules: https://microsoft.github.io/genaiscript/reference/scripts/vector-search/

    const synthesize = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Create a TLA+ specification in a new file ${tlaFile} that formalizes the problem described in ${file.filename}, including all relevant requirements and constraints. Use the **fs_write_file tool** to write the specification. Then, parse the specification using the TLC model checker via the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the specification until it parses successfully. Next, generate a TLC configuration file ${cfgFile}. Use the **tla_tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the config file. Finally, verify the specification using the TLC model checker via the **tla_tlaplus_mcp_tlc_check** tool and determine whether the expected counterexample is found.`
        },
        { model: "github_copilot_chat:current", system: ["system.fs_read_file", "system.fs_write_file"] });
    dbg(synthesize);
    console.log(`Created TLA+ specification: ${synthesize}`);

    // Run TLC manually to check that it exits with the expected exit code.
    // Note: The exit code 12 indicates that TLC found a counterexample, which is what we expect for this task.
    // If TLC does not find a counterexample, it will exit with a different code, and we can cancel the refinement steps.
    const shellOutput = await host.exec(`tlc`, [`${tlaFile}`, `-config`, `${cfgFile}`]);
    if (shellOutput.exitCode !== 12) {
        console.error(`TLC exited with code ${shellOutput.exitCode}. Output: ${shellOutput.stdout}`);
        cancel(`TLC did not exit with expected exit code. Check the output for details.`);
    }
    // workspace.stat

    // Copy the gold standard solution file from the gold/ directory to the workspace root.
    const goldFile = `${fileName}Gold.tla`;
    await workspace.copyFile(`gold/${fileName}Gold.tla`, goldFile)

    // -------- Verify refinement of counterexample with gold standard spec -------- //

    const traceFile = `${fileName}_TTrace_123456789.tla`;
    const traceRefinement = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Use the TLC model checker via the **tla_tlaplus_mcp_tlc_check** tool with the **-generateSpecTE** option to serialize a counterexample trace to a file named ${traceFile} (where 123456789 represents a timestamp) for the TLA+ specification ${tlaFile}. You must not modify either specification directly. Next, create a refinement mapping from ${traceFile} to the gold-standard specification ${goldFile}. Parse the refinement using the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the refinement until it is valid. Once the refinement is correctly parsed, use the **tla_tlaplus_mcp_tlc_check** tool to verify whether the refinement holds.`
        },
        { model: "github_copilot_chat:current", system: ["system.fs_read_file", "system.fs_write_file", "system.fs_find_files"] });
    dbg(traceRefinement);
    console.log(`Created TLA+ trace refinement: ${traceRefinement}`);

    // -------- Verify full refinement of gold standard spec -------- //
    
    const refTLAFile = `${fileName}Ref.tla`;
    const fullRefinement = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Define a refinement mapping from the specification ${tlaFile} to the specification ${fileName}Gold.tla. You must not modify either specification directly. Instead, create a new TLA+ module ${refTLAFile} that extends ${tlaFile} and instantiates ${goldFile}. Parse the refinement module using the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the module until it is valid. Finally, use the **tla_tlaplus_mcp_tlc_check** tool to check whether the refinement mapping holds.`
        },
        { model: "github_copilot_chat:current", system: ["system.fs_read_file", "system.fs_write_file"] });
    dbg(fullRefinement);
    console.log(`Created TLA+ full refinement: ${fullRefinement}`);
}

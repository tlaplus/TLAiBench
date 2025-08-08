script({
    title: "NL2TLA+ translation",
    description: "Translate a natural language description of a TLA+ specification into a TLA+ specification.",
    files: ["puzzles/DieHard.md"],
    systemSafety: false,
    temperature: 0,
    // https://microsoft.github.io/genaiscript/reference/scripts/inline-prompts/#inline-only-scripts
    model: "none",
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

// Helper function to run TLC and validate exit code with custom validation
async function runTLCAndValidate(
    tlaFile: string, 
    cfgFile: string, 
    checkName: string, 
    validateExitCode: (exitCode: number) => boolean,
    extraArgs: string[] = []
) {
    const args = [`-jar`, `tla2tools.jar`, tlaFile, `-config`, cfgFile, `-note`, `-cleanup`, ...extraArgs];
    const result = await host.exec(`java`, args);
    
    if (!validateExitCode(result.exitCode)) {
        console.error(`TLC exited with code ${result.exitCode}. Output: ${result.stdout}. Error: ${result.stderr}`);
        cancel(`${checkName} did not exit with expected exit code. Check the output for details.`);
    }
    
    return result;
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

    if (!file) cancel("no puzzle file provided");

    const baseName = file.filename.replace(/\.[^.]*$/, '');
    const fileName = baseName.split('/').pop();
    const tlaFile = fileName + ".tla";
    const cfgFile = fileName + ".cfg";

    // ------------------------------------------------------------------------------ //
    // -------- Synthesize TLA+ specification -------- //
    // ------------------------------------------------------------------------------ //

    // TODO Import the TLA+ rules with: https://microsoft.github.io/genaiscript/reference/scripts/import-template/
    // Fetch TLC's explain files could be done with: https://microsoft.github.io/genaiscript/reference/scripts/fetch/
    // Alternatively, GenAIScript's vector search could be used to find the relevant rules: https://microsoft.github.io/genaiscript/reference/scripts/vector-search/

    const synthesize = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Create a TLA+ specification in a new file ${tlaFile} that formalizes the problem described in ${file.filename}, including all relevant requirements and constraints. Use the **fs_write_file tool** to write the specification. Then, parse the specification using the TLC model checker via the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the specification until it parses successfully. Next, generate a TLC configuration file ${cfgFile}. Use the **tla_tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the config file. Finally, verify the specification using the TLC model checker via the **tla_tlaplus_mcp_tlc_check** tool and determine whether the expected counterexample is found.`
        },
        { model: "large", system: ["system.fs_read_file", "system.fs_write_file", "system.do_not_explain"] });
    dbg(synthesize);
    console.log(`Created TLA+ specification: ${synthesize}`);

    // ------------------------------------------------------------------------------ //
    // ------ Validate TLA+ specification ------  //
    // ------------------------------------------------------------------------------ //

    // Run TLC manually to check that it exits with the expected exit code.
    // Note: The exit code 12 indicates that TLC found a counterexample, which is what we expect for this task.
    // If TLC does not find a counterexample, it will exit with a different code, and we can cancel the refinement steps.
    await runTLCAndValidate(tlaFile, cfgFile, "Synthesized spec validation", (exitCode) => exitCode === 12);

    // ------------------------------------------------------------------------------ //
    // ------ Synthesize refinement of counterexample with gold standard spec ------  //
    // ------------------------------------------------------------------------------ //

    // Copy the gold standard solution file from the gold/ directory to the workspace root.
    const goldFile = `${fileName}Gold.tla`;
    await workspace.copyFile(`gold/${fileName}Gold.tla`, goldFile)

    const traceFile = `${fileName}Trace.tla`;
    const traceRefFile = `${fileName}TraceRef.tla`;
    const traceCfgFile = `${fileName}TraceRef.cfg`;
    const traceRefinement = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Use the TLC model checker via the **tla_tlaplus_mcp_tlc_check** tool with the **-dumptrace tlcTESpec ${traceFile}** option to serialize a counterexample trace to a file named ${traceFile} for the TLA+ specification ${tlaFile}. Next, create a refinement mapping from ${traceFile} to the gold-standard specification ${goldFile} in a new spec ${traceRefFile} that extends ${traceFile} and refines ${goldFile}. You must not modify ${traceFile} or ${goldFile} specification directly.  Parse the refinement using the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the refinement until it is valid. Once the refinement is correctly parsed, use the **tla_tlaplus_mcp_tlc_check** tool to verify whether the refinement holds. Use the **tla_tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the ${traceCfgFile} config file.`
        },
        { model: "large", system: ["system.fs_read_file", "system.fs_write_file", "system.do_not_explain"] });
    dbg(traceRefinement);
    console.log(`Created TLA+ trace refinement: ${traceRefinement}`);

    // ------------------------------------------------------------------------------ //
    // ------ Validate TLA+ trace refinement specification ------  //
    // ------------------------------------------------------------------------------ //

    // Check if the trace refinement holds by running TLC on the trace file.
    // This is expected to pass, as the trace in the trace file should be a valid behavior of the gold standard specification. 
    await runTLCAndValidate(traceRefFile, traceCfgFile, "Trace refinement validation", (exitCode) => exitCode === 0);
    // However, it might pass for the wrong reason, so we need to check that TLC actually checked a refinement.
    await runTLCAndValidate(traceRefFile, traceCfgFile, "Trace refinement validation with refinement postcondition", (exitCode) => exitCode === 0, [`-postcondition`, `${goldFile}!Refinement`]);
    // Also check that the refinement has the expected state-space statistics.
    await runTLCAndValidate(traceRefFile, traceCfgFile, "Trace refinement validation with stats postcondition", (exitCode) => exitCode === 0, [`-postcondition`, `${goldFile}!Stats`]);

    // ------------------------------------------------------------------------------ //
    // -------- Synthesize full refinement of gold standard spec -------- //
    // ------------------------------------------------------------------------------ //
    
    const refTLAFile = `${fileName}Ref.tla`;
    const refCFGFile = `${fileName}Ref.cfg`;
    const fullRefinement = await runPrompt(
        (ctx) => {
            setupTLATools(ctx);
            ctx.$`Define a refinement mapping from the specification ${tlaFile} to the specification ${fileName}Gold.tla. You must not modify either specification directly. Instead, create a new TLA+ module ${refTLAFile} that extends ${tlaFile} and instantiates ${goldFile}. Parse the refinement module using the **tla_tlaplus_mcp_sany_parse** tool. If parsing fails, revise the module until it is valid. Finally, use the **tla_tlaplus_mcp_tlc_check** tool to check whether the refinement mapping holds.  Use the **tla_tlaplus_mcp_sany_symbol** tool to identify the relevant symbols needed in the ${refCFGFile} config file.`
        },
        { model: "large", system: ["system.fs_read_file", "system.fs_write_file", "system.do_not_explain"] });
    dbg(fullRefinement);
    console.log(`Created TLA+ full refinement: ${fullRefinement}`);

    // ------------------------------------------------------------------------------ //
    // ------ Validate TLA+ full refinement specification ------  //
    // ------------------------------------------------------------------------------ //

    await runTLCAndValidate(traceRefFile, traceCfgFile, "Full refinement validation", (exitCode) => exitCode === 0);
    await runTLCAndValidate(traceRefFile, traceCfgFile, "Full refinement validation with refinement postcondition", (exitCode) => exitCode === 0, [`-postcondition`, `${goldFile}!Refinement`]);
    await runTLCAndValidate(traceRefFile, traceCfgFile, "Full refinement validation with stats postcondition", (exitCode) => exitCode === 0, [`-postcondition`, `${goldFile}!Stats`]);
}

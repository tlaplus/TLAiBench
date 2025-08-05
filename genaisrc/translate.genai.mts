script({
    title: "NL2TLA+ translation",
    description: "Translate a natural language description of a TLA+ specification into a TLA+ specification.",
    temperature: 0,
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
    files: ["puzzles/DieHard.md"],
    // model: "github:openai/o3-mini"
    model: "github_copilot_chat:current"
})
// The TLA+ MCP tools have to be started separately.
defTool({
    tla: {
        url: "http://localhost:59071/mcp",
        type: "http"
    }
})
// See https://github.com/microsoft/genaiscript/issues/1809 why we define fs_write_file.
defTool(
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
)

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
            ctx.defTool({
                tla: {
                    url: "http://localhost:59071/mcp",
                    type: "http"
                }
            });
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
            ctx.$`Formalize the puzzle ${file.filename} using TLA+: Create (see fs_write_file) TLA+ specification in a new ${tlaFile} file that captures the problem's requirements and constraints.  Use the TLC model checker via the tla_tlaplus_mcp_sany_parse to parse the specification. If parsing fails, you will need to fix the specification and try again. Generate a TLC config file ${cfgFile}. Use tla_tlaplus_mcp_sany_symbol to find the symbols in the specification when generating the TLC config file. Once you have a valid TLA+ specification, use the TLC model checker via the tla_tlaplus_mcp_tlc_check tool to check if TLC finds the expected counterexample.`
        },
        { model: "github_copilot_chat:current", modelConcurrency: { "github_copilot_chat:current": 1 }, system: ["system.fs_read_file"] });
    dbg(synthesize);
    console.log(`Created TLA+ specification: ${synthesize}`);

    // Copy the gold standard solution file from the gold/ directory to the workspace root.
    const goldFile = `gold/${fileName}Gold.tla`;
    await workspace.copyFile(goldFile, `${fileName}Gold.tla`)

    // -------- Verify refinement of counterexample with gold standard spec -------- //

    const traceRefinement = await runPrompt(
        (ctx) => {
            ctx.defTool({
                tla: {
                    url: "http://localhost:59071/mcp",
                    type: "http"
                }
            });
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
            ctx.$`Use the TLC model checker via the tla_tlaplus_mcp_tlc_check with the extra option -generateTESpec to serialize the counterexample trace of the TLA+ specification ${tlaFile} to a file.`
        },
        { model: "github_copilot_chat:current", modelConcurrency: { "github_copilot_chat:current": 1 }, system: ["system.fs_read_file"] });
    dbg(traceRefinement);
    console.log(`Created TLA+ trace refinement: ${traceRefinement}`);

    // -------- Verify full refinement of gold standard spec -------- //
    
    const refTLAFile = `${fileName}Ref.tla`;
    const fullRefinement = await runPrompt(
        (ctx) => {
            ctx.defTool({
                tla: {
                    url: "http://localhost:59071/mcp",
                    type: "http"
                }
            });
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
            ctx.$`Create a refinement mapping from specification ${tlaFile} to specification ${fileName}Gold.tla. You are not allowed to move or modify specifications A or B directly. Instead, create a new module ${refTLAFile} that extends ${tlaFile} and instantiates ${goldFile}.  Once you have a valid ${refTLAFile} accepted by tla_tlaplus_mcp_sany_parse, use the TLC model checker via the tla_tlaplus_mcp_tlc_check tool to check if the refinement holds.`
        },
        { model: "github_copilot_chat:current", modelConcurrency: { "github_copilot_chat:current": 1 }, system: ["system.fs_read_file"] });
    dbg(fullRefinement);
    console.log(`Created TLA+ full refinement: ${fullRefinement}`);
}



//     const refCFGFile = `${fileName}Ref.cfg`;


    // workspace.appendText(refCFGFile, ``)
    // // Confirm that the .tla and the .cfg files have been created
    // workspace.findFiles(tlaFile).then(files => {
    //     if (files.length === 0) {
    //         throw new Error(`The TLA+ specification file ${tlaFile} was not created.`);
    //     }
    // });
    // workspace.findFiles(cfgFile).then(cfgFiles => {
    //     if (cfgFiles.length === 0) {
    //         throw new Error(`The TLC config file ${cfgFile} was not created.`);
    //     }
    // });

    // 

    // defFileOutput(fileName + ".tla", "the created TLA+ specification")
    // defFileOutput(fileName + ".cfg", "the created TLC config file")

    // $`Formalize the puzzle ${file.filename} using TLA+: Create (see fs_write_file) TLA+ specification in a new ${tlaFile} file that captures the problem's requirements and constraints.  Use the TLC model checker via the tla_tlaplus_mcp_sany_parse to parse the specification. If parsing fails, you will need to fix the specification and try again. Generate a TLC config file ${cfgFile}. Use tla_tlaplus_mcp_sany_symbol to find the symbols in the specification when generating the TLC config file. Once you have a valid TLA+ specification, use the TLC model checker via the tla_tlaplus_mcp_tlc_check tool to check if TLC finds the expected counterexample that shows the steps to a solution to the puzzle.`

# TLAi+Bench

A dataset and benchmark suite for evaluating Large Language Models (LLMs) on TLA+ formal specification tasks, featuring logic puzzles and real-world scenarios.

## 📌 Context & Motivation

This repository addresses the growing need for systematic evaluation of AI-assisted formal methods development. It stems from two initiatives in the TLA+ community:

- **[TLA+ Dataset Issue](https://github.com/tlaplus/tlaplus/issues/1196)**: A community proposal to create standardized benchmarks for LLM evaluation on TLA+ tasks
- **[TLAi+ Challenge](https://foundation.tlapl.us/challenge/index.html#-announcement-winners-of-the-2025-tlai-challenge)**: The TLA+ Foundation's GenAI-accelerated challenge showcasing innovative work at the intersection of TLA+ and AI

## 🎯 Purpose

TLAi+Bench enables:

- **Consistent LLM Evaluation**: Objective comparison of language model performance on formal specification tasks
- **Tool Development**: Reference benchmarks for AI-assisted TLA+ development tools
- **Agentic Workflow Development**: Foundation for building tool-supported autonomous agents that can iteratively develop, verify, and refine formal specifications
- **Research Advancement**: A standardized dataset for formal methods and AI research
- **Educational Resource**: Well-documented examples for learning TLA+ through practical problems

## 📁 Repository Structure

```
TLAi+Bench/
├── puzzles/                    # Problem descriptions in natural language
│   ├── CabbageGoatWolf.md     # Classic river crossing puzzle
│   ├── CatInABox.md           # Quantum mechanics inspired puzzle
│   ├── CoffeeCan.md           # Probabilistic algorithm puzzle
│   ├── DieHard.md             # Water jug measurement puzzle
│   ├── DiningPhilosophers.md  # Concurrency classic
│   ├── GameOfLife.md          # Cellular automaton
│   ├── Prisoners.md           # Logic and game theory puzzle
│   ├── RiverCrossingFlashlight.md # Optimization puzzle
│   └── TowerOfHanoi.md        # Recursive puzzle
├── gold/                      # Reference TLA+ specifications
│   ├── CatInBoxGold.tla
│   ├── CoffeeCanGold.tla
│   ├── DieHardGold.tla
│   ├── HanoiGold.tla
│   ├── PrisonersGold.tla
│   └── RiverCrossingFlashlightGold.tla
├── genaisrc/                  # AI generation scripts and utilities
│   └── translate.genai.mts    # Main translation script (NL → TLA+)
```

## 🧩 Puzzle Categories

The benchmark includes diverse problem types to test different aspects of formal specification:

1. **Logic Puzzles**: Classic problems requiring constraint modeling (Die Hard, River Crossing)
2. **Concurrency**: Multi-process coordination challenges (Dining Philosophers)
3. **Algorithms**: Formal specification of computational processes (Coffee Can)
4. **Games & Strategy**: Decision-making and game theory (Prisoners)
5. **Mathematical**: Recursive and mathematical structures (Tower of Hanoi)
6. **Simulation**: Dynamic system modeling (Game of Life)

## 🚀 Getting Started

### Prerequisites

- **VSCode**: Required to host the TLA+ MCP servers
  - TLA+ VSCode extension (`tlaplus.vscode-ide`)
  - X11 server (for headless environments)
- **Node.js 24+**: For GenAIScript runtime
- **TLA+ Tools**: 
  - `tla2tools.jar` (nightly build from tlapl.us)
  - `CommunityModules-deps.jar` (latest release)
- **GenAIScript**: For AI-assisted specification generation
  - We use [GenAIScript](https://microsoft.github.io/genaiscript) because it balances programmability with automation—unlike Python scripts (too low-level) or IDE chats (not scriptable). It provides JavaScript-based prompt assembly, MCP tool integration, headless operation for automated benchmarks, and broad support for multiple LLM providers (OpenAI, Azure OpenAI, Anthropic, GitHub Models, local models via Ollama, and more).
  - The development team is highly responsive to issues ([#1872](https://github.com/microsoft/genaiscript/issues/1872), [#1833](https://github.com/microsoft/genaiscript/issues/1833), [#1809](https://github.com/microsoft/genaiscript/issues/1809), ...).

### Running Benchmarks

To run the TLA+ benchmark suite:

```bash
# Run GenAIScript to generate and verify TLA+ specifications
DEBUG=* npx genaiscript@latest run genaisrc/translate.genai.mts

# Or run with specific model configuration
DEBUG=* npx genaiscript@latest run --provider github --model github:openai/gpt-4 genaisrc/translate.genai.mts

# Or run with a specific provider (create an inference profile first (see https://github.com/microsoft/genaiscript/issues/1918))
DEBUG=* npx --yes genaiscript@latest run translate --provider anthropic_bedrock --model anthropic_bedrock:arn:aws:bedrock:us-east-1:024871859028:inference-profile/us.anthropic.claude-sonnet-4-20250514-v1:0
```

If you have a **GitHub Copilot Chat subscription**, you can also [run](https://microsoft.github.io/genaiscript/configuration/github-copilot-chat) the `translate` script directly within VSCode without needing a separate LLM provider. This approach is particularly useful for users who already have GitHub Copilot access and want to leverage those models without additional LLM provider setup. Note that these models are not available from pure command-line usage. Also pay attention to your [budget](https://github.com/settings/billing/usage?query=product:copilot).

The [translate](genaisrc/translate.genai.mts) GenAIScript handles the complete workflow:
- Reads puzzle descriptions from `puzzles/`
- Generates TLA+ specifications using LLMs
- Automatically runs syntax checking and model verification
- Compares results against gold standard specifications

### Evaluation Workflow

1. **Problem Selection**: Choose a puzzle from the `puzzles/` directory
2. **Specification Development**: Create a TLA+ specification based on the natural language description
3. **Verification**: Use TLC to model check your specification
4. **Comparison**: Compare against the gold standard in `gold/`

## 📊 Evaluation Criteria

Synthesized specifications are evaluated against gold standard specifications using:

- **Counterexample Analysis**: Does the synthesized spec produce the expected counterexample when model checked?
- **Refinement Checking**: Does the synthesized specification refine the gold standard specification?
- **Behavioral Equivalence**: Are the allowed behaviors consistent with the gold standard specification?
- **Property Satisfaction**: Does the spec satisfy the same safety and liveness properties as the gold standard?

## 🤝 Contributing

We welcome contributions to expand the benchmark:

1. **New Puzzles**: Add problem descriptions and gold standard specifications
2. **Evaluation Tools**: Improve automated scoring and comparison utilities
3. **Documentation**: Enhance problem descriptions and solution explanations
4. **Validation**: Help verify and improve existing specifications

## 📚 Related Work

- [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- [TLA+ Community Modules](https://github.com/tlaplus/CommunityModules)
- [TLA+ Examples](https://github.com/tlaplus/Examples)
- [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html) - Leslie Lamport's TLA+ book

## 🏆 Acknowledgments

This work is inspired by and contributes to:

- The TLA+ Foundation's mission to advance formal methods
- The TLAi+ Challenge winners who demonstrated innovative AI-assisted TLA+ development
- The broader TLA+ community's collaborative efforts

## 📄 License

This project is released under the MIT License, following the TLA+ community's open-source principles.

---

*For questions, suggestions, or collaboration opportunities, please open an issue in this repository or engage with the broader TLA+ community.*

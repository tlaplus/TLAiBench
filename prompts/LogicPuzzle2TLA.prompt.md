---
description: 'Formalize a logic puzzle using TLA+, use TLC to find the solution.'
mode: 'agent'
model: Claude Sonnet 4
tools: ['search', 'editFiles', 'runTasks', 'tlaplus_check', 'tlaplus_parse', 'tlaplus_symbol', 'tlaplus_smoke', 'tlaplus_explore']
---

Formalize all puzzles in #../puzzles/ using TLA+ (use the instructions below). You will need to create a TLA+ specification that captures the problem's requirements and constraints, then use the TLC model checker to explore possible solutions. You're done when you have a TLA+ specification that correctly models the problem and can be checked with TLC to find a solution.

# 📘 How to Create a TLA+ Specification from a Prose Description

TLA+ (Temporal Logic of Actions) is a formal specification language used to design, model, and verify systems. Follow these steps to systematically convert a prose description into a precise TLA+ specification.

---

## 🧩 Step 1: Understand the Prose Description

* **Carefully read the problem** to understand:

  * **Entities:** What are the components (e.g., processes, clients, servers)?
  * **State:** What data or configuration defines the state of the system?
  * **Actions:** What operations change the state?
  * **Invariants and Goals:** What must always be true? What is the system trying to achieve?

> 💡 Tip: Draw diagrams or write summaries to solidify understanding.

---

## 🧱 Step 2: Identify the System State

* Create a list of **state variables** that fully describe the system at any moment.

  * These are the variables you'll define in the `VARIABLES` clause.

**Example:**

```tla
VARIABLES x, y, turn, flag
```

* Consider sets, functions like sequences or records, etc., to model structured data.

---

## ⚙️ Step 3: Define the Initial State (`Init`)

* Write a predicate (`Init`) that specifies the **initial values** of your variables.

**Example:**

```tla
Init == /\ x = 0
         /\ y = 0
         /\ turn = 0
         /\ flag = [i \in {0, 1} |-> FALSE]
```

---

## 🔄 Step 4: Specify the Actions (`Next`)

* Define **actions** that describe how the system can move from one state to another.
* Each action is a predicate involving **current** and **next** state variables (use `'` to indicate the next state).

**Example:**

```tla
IncrementX == x' = x + 1 /\ UNCHANGED <<y, turn, flag>>
ToggleFlag(i) == flag' = [flag EXCEPT ![i] = ~@] /\ UNCHANGED <<x, y, turn>>
```

* Combine all possible actions into a `Next` predicate:

```tla
Next == \/ IncrementX
        \/ \E i \in {0, 1} : ToggleFlag(i)
```

---

## 🔒 Step 5: State the Invariants

* Identify **properties that must always hold** (e.g., mutual exclusion, value bounds).
* Use these for both specification clarity and model checking.

**Example:**

```tla
Invariant == x >= 0 /\ y >= 0
```

---

## 🧮 Step 6: Define the Complete Specification

Use TLA+'s temporal logic to combine the initial state and the next-state relation.

```tla
Spec == Init /\ [][Next]_<<x, y, turn, flag>>
```

This defines the **entire behavior** of the system over time.

---

## 🔍 Step 7: Use TLC to Model Check

* Write a `TLC` configuration file (`.cfg`) to define constants, invariants, and properties.

**Example: `MySpec.cfg`**

```tla
INIT Init
NEXT Next
INVARIANT Invariant
```

* Run the TLC model checker to validate behavior, check invariants, or find counterexamples.

---

## 🛠 Step 8: Iterate and Refine

* Based on TLC feedback or further system understanding:

  * Add missing actions or constraints.
  * Refactor states or data structures.
  * Improve naming and structure for clarity.

---

## ✅ Summary Checklist

| Step | Description               |
| ---- | ------------------------- |
| 1    | Understand the problem    |
| 2    | Identify state variables  |
| 3    | Define `Init`             |
| 4    | Define actions and `Next` |
| 5    | Write invariants          |
| 6    | Combine into `Spec`       |
| 7    | Use TLC to model check    |
| 8    | Iterate and refine        |

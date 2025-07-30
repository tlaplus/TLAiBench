* Do not use temporal properties (`PROPERTY` or `PROPERTIES`) when modeling logic puzzles with TLA+. Instead, to find a solution using TLC, express the negation of the goal state as an ordinary safety property (`INVARIANT`).

* There is no reason to create a variable to remember the steps of the solution.  TLC will print the counterexample to the negated goal state.

* Do not write a PlusCal algorithm. Always write a TLA+ specification.

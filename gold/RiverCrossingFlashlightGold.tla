---------------------------- MODULE RiverCrossingFlashlightGold ---------------------------
EXTENDS Naturals, FiniteSets, TLC, Sequences

CONSTANT MaxLevel
ASSUME MaxLevel \in Nat

CONSTANT Cost
ASSUME 
    /\ DOMAIN Cost \in SUBSET STRING
    /\ \A n \in DOMAIN Cost: Cost[n] \in Nat

MyCost == [
    A |-> 10,
    B |-> 5,
    C |-> 2,
    D |-> 1
]

VARIABLES left, right, flashlightLeft, flashlightLevel
vars == <<left, right, flashlightLeft, flashlightLevel>>

People == DOMAIN Cost

TypeOK ==
    /\ left \subseteq People
    /\ right \subseteq People
    /\ flashlightLeft \in BOOLEAN 
    /\ flashlightLevel \in Nat

(* Initial state: all People and the flashlight are on the left side.
   The spare flashlight is fully charged.   *)
Init ==
    /\ left = People
    /\ right = {}
    /\ flashlightLeft = TRUE
    /\ flashlightLevel = MaxLevel

(* Action: from one or two people left to right *)
LeftToRight(group, cost) ==
    (* Before the move: *)
    (* The group must be non-empty and contain at most two people *)
    /\ Cardinality(group) \in 1..2
    (* Can only move people to the right that are on the left side *)
    /\ group \in SUBSET left
    (* The flashlight has to be left *)
    /\ flashlightLeft = TRUE
    (* After the move: *)
    (* The flashlight will be on the right side *)
    /\ flashlightLeft' = ~flashlightLeft
    (* The group of people will be removed from the left side *)
    /\ left' = left \ group
    (* The group of people will be added to the right side *)
    /\ right' = right \union group
    (* The flashlight will be decreased by the cost of moving the 
       slowest person of the group *)
    /\ flashlightLevel' = flashlightLevel - cost

(* Action: from right to left *)
RightToLeft(group, cost) ==
    /\ Cardinality(group) \in 1..2
    /\ group \in SUBSET right
    /\ flashlightLeft = FALSE
    /\ flashlightLeft' = ~flashlightLeft
    /\ right' = right \ group
    /\ left' = left \union group
    /\ flashlightLevel' = flashlightLevel - cost

Max(S) ==
    CHOOSE e \in S: \A x \in S: e >= x

(* Next-state relation *)
Next ==
    \/ \E group \in (SUBSET People) \ {{}} :
        \E c \in {Max({ Cost[g] : g \in group })} :
            LeftToRight(group, c)
    \/ \E group \in (SUBSET People) \ {{}} :
        \E c \in {Max({ Cost[g] : g \in group })} :
            RightToLeft(group, c)

(* Safety: People cannot be on both sides and don't disappear or duplicate *)
Safety ==
    /\ left \intersect right = {}
    /\ left \union right = People

(* All People are on the right side and the flashlight is not depleted *)
Solution ==
    /\ right = People
    /\ flashlightLevel >= 0

(* This invariant will be violated when we find a solution *)
NoSolution ==
    ~Solution

(* Specification *)
Spec == 
    Init /\ [][Next]_vars

====
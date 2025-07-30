---
applyTo: '**/*.tla'
---

## Table of Contents

1. [Functions](#functions)
2. [SequencesExt](#sequences-extension)
3. [BagsExt](#bags-extension)
4. [FiniteSetsExt](#finitesets-extension)
5. [Relation](#relation)
6. [Graphs](#graphs)
7. [Undirected Graphs](#undirected-graphs)

## Functions

The `Functions` module provides operators for working with TLA+ functions, including operations like restriction, injection, and function properties.

### Restrict(f, S)

Restricts a function to a set (should be a subset of the domain).

**Example:**
```tla
LET f == [x \in 0..9 |-> x*x]
    S == {0, 2, 4}
IN Restrict(f, S) = (0 :> 0 @@ 2 :> 4 @@ 4 :> 16)
```

### RestrictDomain(f, Test(_))

Restricts a function to the subset of its domain satisfying a test predicate.

**Example:**
```tla
LET f == [x \in 0..9 |-> x*x]
IN RestrictDomain(f, LAMBDA x : x % 2 = 0) = (0 :> 0 @@ 2 :> 4 @@ 4 :> 16 @@ 6 :> 36 @@ 8 :> 64)
```

### RestrictValues(f, Test(_))

Restricts a function to the subset of its domain for which the function values satisfy a test predicate.

**Example:**
```tla
LET f == [x \in 0..9 |-> x*x]
IN RestrictValues(f, LAMBDA y : y % 4 = 0) = (0 :> 0 @@ 2 :> 4 @@ 4 :> 16 @@ 6 :> 36 @@ 8 :> 64)
```

### IsRestriction(narrow, wide)

Checks if one function is a restriction of another. That is, the domain of `narrow` is a subset of the domain of `wide`, and for each element in the domain of `narrow`, the function values are the same.

**Example:**
```tla
IsRestriction([one |-> 1], [one |-> 1, two |-> 2]) = TRUE
IsRestriction([one |-> 1, two |-> 2], [one |-> 1, two |-> 3]) = FALSE
```

### Range(f)

Returns the range (codomain) of a function.

**Example:**
```tla
Range([x \in 1..3 |-> x*x]) = {1, 4, 9}
```

### Pointwise(f, g, T(_,_))

Applies a binary operation to corresponding elements of two functions.

**Example:**
```tla
LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)
    g == ("a" :> 1 @@ "b" :> 1 @@ "c" :> 3)
IN Pointwise(f, g, LAMBDA x, y: x + y) = ("a" :> 1 @@ "b" :> 2 @@ "c" :> 5)
```

### Inverse(f, S, T)

Creates the inverse function of `f` from domain `S` to range `T`.

**Example:**
```tla
LET f == ("a" :> 0 @@ "b" :> 1 @@ "c" :> 2)
IN Inverse(f, DOMAIN f, Range(f)) = (0 :> "a" @@ 1 :> "b" @@ 2 :> "c")
```

### AntiFunction(f)

Creates the inverse of a function.

**Example:**
```tla
AntiFunction(<<"a", "b", "c">>) = [a |-> 1, b |-> 2, c |-> 3]
```

### IsInjective(f)

Checks if a function is injective (one-to-one).

**Example:**
```tla
IsInjective([i \in 1..10 |-> i]) = TRUE
IsInjective([a: 1, b: 1]) = FALSE
```

### Injection(S, T)

Returns the set of all injective functions from set `S` to set `T`.

**Example:**
```tla
Injection({1, 2}, {3, 4, 5}) = {[1 |-> 3, 2 |-> 4], [1 |-> 3, 2 |-> 5], [1 |-> 4, 2 |-> 3], [1 |-> 4, 2 |-> 5], [1 |-> 5, 2 |-> 3], [1 |-> 5, 2 |-> 4]}
```

### Surjection(S, T)

Returns the set of all surjective functions from set `S` to set `T`.

**Example:**
```tla
Surjection({1, 2, 3}, {4, 5}) = {[1 |-> 4, 2 |-> 5, 3 |-> 4], [1 |-> 4, 2 |-> 5, 3 |-> 5], [1 |-> 5, 2 |-> 4, 3 |-> 4], [1 |-> 5, 2 |-> 4, 3 |-> 5]}
```

### Bijection(S, T)

Returns the set of all bijective functions (one-to-one and onto) from set `S` to set `T`.

**Example:**
```tla
Bijection({1, 2}, {3, 4}) = {[1 |-> 3, 2 |-> 4], [1 |-> 4, 2 |-> 3]}
```

### ExistsInjection(S, T), ExistsSurjection(S, T), ExistsBijection(S, T)

Check if an injection, surjection, or bijection exists between sets `S` and `T`.

**Example:**
```tla
ExistsInjection({1, 2}, {3, 4, 5}) = TRUE
ExistsSurjection({1, 2}, {3, 4, 5}) = FALSE
ExistsBijection({1, 2}, {3, 4}) = TRUE
```

### FoldFunction(op(_, _), base, fun)

Applies a binary function to all elements of a function in arbitrary order.

**Example:**
```tla
FoldFunction(LAMBDA x, y: {x} \cup y, {}, <<1, 2, 1>>) = {1, 2}
```

### FoldFunctionOnSet(op(_, _), base, fun, indices)

Applies a binary function to elements of a function at specific indices.

**Example:**
```tla
FoldFunctionOnSet(LAMBDA x, y: {x} \cup y, {}, [n \in 1..9999 |-> n], 2..9998) = 2..9998
```

## SequencesExt

The `SequencesExt` module extends the standard `Sequences` module with additional operators for working with sequences.

### ToSet(s)

Convert a sequence to a set (removing duplicates).

**Example:**
```tla
ToSet(<<1, 2, 1, 3>>) = {1, 2, 3}
```

### SetToSeq(S)

Convert a set to a sequence that contains all the elements of the set exactly once.

**Example:**
```tla
LET seq == SetToSeq({1, 2, 3})
IN Len(seq) = 3 /\ ToSet(seq) = {1, 2, 3}
```

### SetToSeqs(S)

Convert a set to all possible sequences containing its elements once with no duplicates.

**Example:**
```tla
SetToSeqs({"a", "b"}) = {<<"a", "b">>, <<"b", "a">>}
```

### SetToSortSeq(S, op(_,_))

Convert a set to a sorted sequence using the comparison operator `op`.

**Example:**
```tla
SetToSortSeq({3, 1, 2}, LAMBDA x, y: x < y) = <<1, 2, 3>>
```

### SetToAllKPermutations(S)

Convert a set to all possible k-permutations for all k from 0 to the cardinality of the set.

**Example:**
```tla
SetToAllKPermutations({"a", "b"}) = {<<>>, <<"a">>, <<"b">>, <<"a", "b">>, <<"b", "a">>}
```

### TupleOf(set, n)

Generate all n-tuples with elements from the given set.

**Example:**
```tla
TupleOf({0, 1}, 2) = {<<0, 0>>, <<0, 1>>, <<1, 0>>, <<1, 1>>}
```

### SeqOf(set, n)

Generate all sequences up to length n with elements from the given set.

**Example:**
```tla
SeqOf({0, 1}, 2) = {<<>>, <<0>>, <<1>>, <<0, 0>>, <<0, 1>>, <<1, 0>>, <<1, 1>>}
```

### BoundedSeq(S, n)

An alias for SeqOf.

**Example:**
```tla
BoundedSeq({0, 1}, 2) = {<<>>, <<0>>, <<1>>, <<0, 0>>, <<0, 1>>, <<1, 0>>, <<1, 1>>}
```

### Contains(s, e)

Test whether element `e` is in sequence `s`.

**Example:**
```tla
Contains(<<1, 2, 3>>, 2) = TRUE
Contains(<<1, 2, 3>>, 4) = FALSE
```

### Reverse(s)

Reverse the given sequence.

**Example:**
```tla
Reverse(<<1, 2, 3>>) = <<3, 2, 1>>
```

### Remove(s, e)

Remove all occurrences of element `e` from sequence `s`.

**Example:**
```tla
Remove(<<"a", "a", "b">>, "a") = <<"b">>
```

### ReplaceAll(s, old, new)

Replace all occurrences of `old` with `new` in sequence `s`.

**Example:**
```tla
ReplaceAll(<<1, 1, 2, 1, 1, 3>>, 1, 4) = <<4, 4, 2, 4, 4, 3>>
```

### ReplaceAt(s, i, e)

Replace the element at position `i` in sequence `s` with element `e`.

**Example:**
```tla
ReplaceAt(<<1, 1, 1>>, 1, 2) = <<2, 1, 1>>
```

### IsPrefix(s, t)

Test whether sequence `s` is a prefix of sequence `t`.

**Example:**
```tla
IsPrefix(<<1, 2>>, <<1, 2, 3>>) = TRUE
IsPrefix(<<1, 3>>, <<1, 2, 3>>) = FALSE
```

### IsStrictPrefix(s, t)

Test whether sequence `s` is a strict prefix of sequence `t`.

**Example:**
```tla
IsStrictPrefix(<<1, 2>>, <<1, 2, 3>>) = TRUE
IsStrictPrefix(<<1, 2>>, <<1, 2>>) = FALSE
```

### IsSuffix(s, t)

Test whether sequence `s` is a suffix of sequence `t`.

**Example:**
```tla
IsSuffix(<<2, 3>>, <<1, 2, 3>>) = TRUE
IsSuffix(<<1, 3>>, <<1, 2, 3>>) = FALSE
```

### IsStrictSuffix(s, t)

Test whether sequence `s` is a strict suffix of sequence `t`.

**Example:**
```tla
IsStrictSuffix(<<2, 3>>, <<1, 2, 3>>) = TRUE
IsStrictSuffix(<<1, 2, 3>>, <<1, 2, 3>>) = FALSE
```

### FoldLeft(op(_, _), base, seq)

Fold a sequence from left to right.

**Example:**
```tla
FoldLeft(+, 0, <<1, 2, 3, 4>>) = 10
```

### FoldRight(op(_, _), seq, base)

Fold a sequence from right to left.

**Example:**
```tla
FoldRight(-, <<1, 2, 3>>, 0) = 2  \* 1 - (2 - (3 - 0)) = 1 - (2 - 3) = 1 - (-1) = 2
```

## BagsExt

The `BagsExt` module provides additional operators on bags (multisets), extending the standard TLA+ functionality for working with bags.

### BagAdd(B, x)

Adds an element `x` to bag `B`. Equivalent to `B (+) SetToBag({x})`.

**Example:**
```tla
LET B == SetToBag({1, 2}) 
IN BagAdd(B, 2) = B (+) SetToBag({2})  \* Adds one more occurrence of element 2

LET B == SetToBag({1, 2}) 
IN BagAdd(B, 3) = B (+) SetToBag({3})  \* Adds element 3 that wasn't in the bag
```

### BagRemove(B, x)

Removes one occurrence of element `x` from bag `B`. Equivalent to `B (-) SetToBag({x})`.

**Example:**
```tla
LET B == SetToBag({1, 2})
IN BagRemove(B, 2) = SetToBag({1})  \* Removes one occurrence of element 2

LET B == (1 :> 2) @@ (2 :> 1)  \* Bag with two 1's and one 2
IN BagRemove(B, 1) = (1 :> 1) @@ (2 :> 1)  \* Removes one occurrence of element 1
```

### BagRemoveAll(B, x)

Removes all occurrences of element `x` from bag `B`.

**Example:**
```tla
LET B == (1 :> 2) @@ (2 :> 1)  \* Bag with two 1's and one 2
IN BagRemoveAll(B, 1) = (2 :> 1)  \* Removes all occurrences of element 1
```

### MapThenFoldBag(op(_, _), base, f(_), choose(_), B)

Fold operation `op` over the images through `f` of all elements of bag `B`, starting from `base`. The parameter `choose` indicates the order in which elements of the bag are processed.

**Example:**
```tla
MapThenFoldBag(LAMBDA x, y: x + y,  \* Sum function
               0,                   \* Starting value
               LAMBDA x: 1,         \* Map each element to 1 (for counting)
               LAMBDA B: CHOOSE x \in DOMAIN B: TRUE,  \* Choose any element
               (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)) = 6  \* Count of elements in bag
```

### FoldBag(op(_, _), base, B)

Fold operation `op` over all elements of bag `B`, starting with value `base`.

**Example:**
```tla
FoldBag(LAMBDA x, y: x + y,  \* Sum function
        0,                   \* Starting value
        (1 :> 2) @@ (2 :> 1) @@ (3 :> 3)) = 13  \* (1*2 + 2*1 + 3*3)
```

### SumBag(B)

Compute the sum of the elements of bag `B`.

**Example:**
```tla
SumBag((1 :> 2) @@ (2 :> 1) @@ (3 :> 2)) = 10  \* (1*2 + 2*1 + 3*2)
```

### ProductBag(B)

Compute the product of the elements of bag `B`.

**Example:**
```tla
ProductBag((2 :> 2) @@ (3 :> 1)) = 12  \* (2^2 * 3^1)
```

## FiniteSetsExt

The `FiniteSetsExt` module extends the standard `FiniteSets` module with additional operators for working with finite sets.

### FoldSet(op(_, _), base, set)

Fold operation `op` over the elements of `set` using `base` as starting value.

**Example:**
```tla
FoldSet(LAMBDA x, y: x + y, 0, 0..10) = 55  \* Sum of integers from 0 to 10
```

### SumSet(set)

Calculate the sum of the elements in `set`.

**Example:**
```tla
SumSet(0..10) = 55  \* Sum of integers from 0 to 10
```

### ProductSet(set)

Calculate the product of the elements in `set`.

**Example:**
```tla
ProductSet(1..3) = 6  \* 1 * 2 * 3
```

### ReduceSet(op(_, _), set, acc)

An alias for `FoldSet`. `ReduceSet` was used instead of `FoldSet` in earlier versions of the community modules.

**Example:**
```tla
ReduceSet(LAMBDA x, y: x + y, {1, 2, 3}, 0) = 6  \* Sum of 1, 2, and 3
```

### MapThenSumSet(op(_), set)

Calculate the sum of projections of the elements in a set.

**Example:**
```tla
MapThenSumSet(LAMBDA e: e.n, {[n |-> 0], [n |-> 1], [n |-> 2]}) = 3  \* Sum of n field values
```

### FlattenSet(S)

Flatten a set of sets into a single set.

**Example:**
```tla
FlattenSet({{1, 2}, {3, 4}}) = {1, 2, 3, 4}
```

### SymDiff(A, B)

The symmetric difference of two sets. Returns elements that are in either set but not in their intersection.

**Example:**
```tla
SymDiff({1, 2, 3}, {2, 3, 4}) = {1, 4}
```

### Quantify(S, P(_))

Count the elements in `S` matching the predicate `P`.

**Example:**
```tla
Quantify(1..9, LAMBDA n: n % 2 = 0) = 4  \* Count of even numbers between 1 and 9
```

### kSubset(k, S)

Return the set of all subsets of `S` that have cardinality `k`.

**Example:**
```tla
kSubset(2, 1..3) = {{1, 2}, {1, 3}, {2, 3}}  \* All 2-element subsets of {1, 2, 3}
```

### Max(S)

Return the maximum element of a finite, non-empty set `S` of integers.

**Example:**
```tla
Max({1, 5, 3}) = 5
```

### Min(S)

Return the minimum element of a finite, non-empty set `S` of integers.

**Example:**
```tla
Min({1, 5, 3}) = 1
```

### Choices(Sets)

Compute all sets that contain one element from each of the input sets.

**Example:**
```tla
Choices({{1, 2}, {2, 3}, {5}}) = {{2, 5}, {1, 2, 5}, {1, 3, 5}, {2, 3, 5}}
```

### ChooseUnique(S, P(_))

Choose a unique element from the input set matching the predicate `P`. Fails if there is no such element or more than one.

**Example:**
```tla
ChooseUnique({2, 3, 4, 5}, LAMBDA x: x % 3 = 1) = 4  \* 4 is the only element divisible by 3 with remainder 1
```

## Relation

The `Relation` module provides operators for testing properties of relations.

### IsReflexive(R, S)

Test whether relation `R` is reflexive over set `S`.

**Example:**
```tla
IsReflexive([<<x, y>> \in {1, 2} \X {1, 2} |-> x = y], {1, 2}) = TRUE
```

### IsReflexiveUnder(op(_, _), S)

Test whether relation defined by `op` is reflexive over set `S`.

**Example:**
```tla
IsReflexiveUnder(=, {0, 1, 2, 3}) = TRUE
IsReflexiveUnder(<, {0, 1, 2, 3}) = FALSE
```

### IsIrreflexive(R, S)

Test whether relation `R` is irreflexive over set `S`.

**Example:**
```tla
IsIrreflexive([<<x, y>> \in {1, 2} \X {1, 2} |-> x < y], {1, 2}) = TRUE
```

### IsIrreflexiveUnder(op(_, _), S)

Test whether relation defined by `op` is irreflexive over set `S`.

**Example:**
```tla
IsIrreflexiveUnder(<, {0, 1, 2, 3}) = TRUE
IsIrreflexiveUnder(=, {0, 1, 2, 3}) = FALSE
```

### IsSymmetric(R, S)

Test whether relation `R` is symmetric over set `S`.

**Example:**
```tla
IsSymmetric([<<x, y>> \in {1, 2} \X {1, 2} |-> x = y], {1, 2}) = TRUE
```

### IsSymmetricUnder(op(_, _), S)

Test whether relation defined by `op` is symmetric over set `S`.

**Example:**
```tla
IsSymmetricUnder(=, {0, 1, 2, 3}) = TRUE
IsSymmetricUnder(<, {0, 1, 2, 3}) = FALSE
```

### IsAntiSymmetric(R, S)

Test whether relation `R` is antisymmetric over set `S`.

**Example:**
```tla
IsAntiSymmetric([<<x, y>> \in {1, 2} \X {1, 2} |-> x <= y], {1, 2}) = TRUE
```

### IsAntiSymmetricUnder(op(_, _), S)

Test whether relation defined by `op` is antisymmetric over set `S`.

**Example:**
```tla
IsAntiSymmetricUnder(<=, {0, 1, 2, 3}) = TRUE
```

### IsAsymmetric(R, S)

Test whether relation `R` is asymmetric over set `S`.

**Example:**
```tla
IsAsymmetric([<<x, y>> \in {1, 2} \X {1, 2} |-> x < y], {1, 2}) = TRUE
```

### IsAsymmetricUnder(op(_, _), S)

Test whether relation defined by `op` is asymmetric over set `S`.

**Example:**
```tla
IsAsymmetricUnder(<, {0, 1, 2, 3}) = TRUE
IsAsymmetricUnder(=, {0, 1, 2, 3}) = FALSE
```

### IsTransitive(R, S)

Test whether relation `R` is transitive over set `S`.

**Example:**
```tla
IsTransitive([<<x, y>> \in {1, 2, 3} \X {1, 2, 3} |-> x < y], {1, 2, 3}) = TRUE
```

### IsTransitiveUnder(op(_, _), S)

Test whether relation defined by `op` is transitive over set `S`.

**Example:**
```tla
IsTransitiveUnder(<, {0, 1, 2, 3}) = TRUE
```

### IsStrictlyPartiallyOrdered(R, S)

Test whether set `S` is strictly partially ordered under relation `R`.

**Example:**
```tla
IsStrictlyPartiallyOrdered([<<x, y>> \in {1, 2, 3} \X {1, 2, 3} |-> x < y], {1, 2, 3}) = TRUE
```

### IsStrictlyPartiallyOrderedUnder(op(_, _), S)

Test whether set `S` is strictly partially ordered under relation defined by `op`.

**Example:**
```tla
IsStrictlyPartiallyOrderedUnder(<, {0, 1, 2, 3}) = TRUE
```

### IsPartiallyOrdered(R, S)

Test whether set `S` is (weakly) partially ordered under relation `R`.

**Example:**
```tla
IsPartiallyOrdered([<<x, y>> \in {1, 2, 3} \X {1, 2, 3} |-> x <= y], {1, 2, 3}) = TRUE
```

### IsPartiallyOrderedUnder(op(_, _), S)

Test whether set `S` is (weakly) partially ordered under relation defined by `op`.

**Example:**
```tla
IsPartiallyOrderedUnder(<=, {0, 1, 2, 3}) = TRUE
```

### IsStrictlyTotallyOrdered(R, S)

Test whether set `S` is strictly totally ordered under relation `R`.

**Example:**
```tla
IsStrictlyTotallyOrdered([<<x, y>> \in {1, 2, 3} \X {1, 2, 3} |-> x < y], {1, 2, 3}) = TRUE
```

### IsStrictlyTotallyOrderedUnder(op(_, _), S)

Test whether set `S` is strictly totally ordered under relation defined by `op`.

**Example:**
```tla
IsStrictlyTotallyOrderedUnder(<, {0, 1, 2, 3}) = TRUE
```

### IsTotallyOrdered(R, S)

Test whether set `S` is totally ordered under relation `R`.

**Example:**
```tla
IsTotallyOrdered([<<x, y>> \in {1, 2, 3} \X {1, 2, 3} |-> x <= y], {1, 2, 3}) = TRUE
```

### IsTotallyOrderedUnder(op(_, _), S)

Test whether set `S` is totally ordered under relation defined by `op`.

**Example:**
```tla
IsTotallyOrderedUnder(<=, {0, 1, 2, 3}) = TRUE
```

## Graphs

The `Graphs` module provides operators for working with directed graphs.

### IsDirectedGraph(G)

Tests whether `G` is a directed graph.

**Example:**
```tla
IsDirectedGraph([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]) = TRUE
```

### DirectedSubgraph(G)

Return the set of all directed subgraphs of `G`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
IN [node |-> {1, 2}, edge |-> {<<1, 2>>}] \in DirectedSubgraph(G)
```

### Transpose(G)

Return the transpose of a directed graph `G` (reverse all edges).

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
IN Transpose(G) = [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 2>>}]
```

### IsUndirectedGraph(G)

Tests whether `G` is an undirected graph (represented as a directed graph with symmetric edges).

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>}]
IN IsUndirectedGraph(G) = TRUE
```

### UndirectedSubgraph(G)

Return the set of all undirected subgraphs of `G`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>}]
IN [node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}] \in UndirectedSubgraph(G)
```

### Path(G)

Return the set of all paths in graph `G`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
IN <<1, 2, 3>> \in Path(G)
```

### SimplePath(G)

Return the set of all simple paths in graph `G` (paths with no repeated nodes).

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
IN <<1, 2, 3>> \in SimplePath(G) /\ <<1, 2, 3, 1>> \notin SimplePath(G)
```

### AreConnectedIn(m, n, G)

Test whether nodes `m` and `n` are connected in graph `G` (there is a path from `m` to `n`).

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
IN AreConnectedIn(1, 3, G) = TRUE
```

### ConnectionsIn(G)

Compute a Boolean matrix that indicates, for each pair of nodes, if there exists a path linking the two nodes.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}]
    C == ConnectionsIn(G)
IN C[1, 3] = TRUE /\ C[3, 1] = FALSE
```

### IsStronglyConnected(G)

Test whether graph `G` is strongly connected.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}]
IN IsStronglyConnected(G) = TRUE
```

### IsTreeWithRoot(G, r)

Test whether graph `G` is a tree with root `r`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {<<2, 1>>, <<3, 1>>}]
IN IsTreeWithRoot(G, 1) = TRUE
```

## Undirected Graphs

The `UndirectedGraphs` module provides operators for working with undirected graphs.

### IsUndirectedGraph(G)

Test whether `G` is an undirected graph (edges are represented as sets {a,b}).

**Example:**
```tla
IsUndirectedGraph([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}]) = TRUE
```

### IsLoopFreeUndirectedGraph(G)

Test whether `G` is an undirected graph with no self-loops.

**Example:**
```tla
IsLoopFreeUndirectedGraph([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}]) = TRUE
```

### UndirectedSubgraph(G)

Return the set of all undirected subgraphs of `G`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}]
IN [node |-> {1, 2}, edge |-> {{1, 2}}] \in UndirectedSubgraph(G)
```

### Path(G)

Return the set of all paths in undirected graph `G`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}]
IN <<1, 2, 3>> \in Path(G)
```

### SimplePath(G)

Return the set of all simple paths in undirected graph `G` (paths with no repeated nodes).

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}]
IN <<1, 2, 3>> \in SimplePath(G)
```

### ConnectedComponents(G)

Compute the connected components of an undirected graph.

**Example:**
```tla
LET G == [node |-> {1, 2, 3, 4}, edge |-> {{1, 2}, {3, 4}}]
IN ConnectedComponents(G) = {{1, 2}, {3, 4}}
```

### AreConnectedIn(m, n, G)

Test whether nodes `m` and `n` are connected in undirected graph `G`.

**Example:**
```tla
LET G == [node |-> {1, 2, 3, 4}, edge |-> {{1, 2}, {3, 4}}]
IN AreConnectedIn(1, 2, G) = TRUE /\ AreConnectedIn(1, 3, G) = FALSE
```

### IsStronglyConnected(G)

Test whether undirected graph `G` is strongly connected (has a single connected component).

**Example:**
```tla
LET G == [node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}]
IN IsStronglyConnected(G) = TRUE
```
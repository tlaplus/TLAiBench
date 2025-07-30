---
description: 'Create a refinement mapping from one spec to another.'
mode: 'agent'
model: Claude Sonnet 4
tools: ['search', 'editFiles', 'runTasks', 'tlaplus_check', 'tlaplus_parse', 'tlaplus_symbol']
---

Create a refinement mapping from specification A to specification B. Do this for the following specifications:

| A                             | B                                      |
|-------------------------------|-----------------------------------     |
| `DieHard.tla`                 | `gold/DieHardGold.tla`                 |
| `CoffeeCan.tla`               | `gold/CoffeeCanGold.tla`               |
| `RiverCrossingFlashlight.tla` | `gold/RiverCrossingFlashlightGold.tla` |
| `Prisoners.tla`               | `gold/PrisonersGold.tla`               |
| `TowerOfHanoi.tla`            | `gold/TowerOfHanoiGold.tla`            |

You are not allowed to move or modify specifications A or B directly. Instead, create a new module C that extends A and instantiates B.

In module C, define a refinement mapping that establishes the correspondence between the constants and variables of A and those of B. This refinement mapping express how the set of behaviors of B is a superset of the set of behaviors specified in A.

### Example

```tla
------ MODULE A ------
CONSTANTS A, B

VARIABLES x, y

Spec == ...
=======
```

```tla
------ MODULE B ------
CONSTANTS C, D

VARIABLES v1, v2

Spec == ...
=======
```

```tla
------ MODULE C ------
EXTENDS A

B == INSTANCE B WITH 
    A <- D,
    B <- C,
    x <- v1,
    y <- v2

BSpec == B!Spec

THEOREM Spec => BSpec
=======
```
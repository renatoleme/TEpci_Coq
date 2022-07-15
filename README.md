# Ecumenical tableaux

In _On the unity of logic_, J.-Y. Girard asks whether is it possible to handle the well-known distinction between "classical" and "intuitionistic" not through a change of system, but through "a change of formulas." While considering different but related thoughts, Krauss figured that, with the adequated ground, such a system would offer a "constructively valid refinement of classical reasoning.'' Interestingly enough, this pluralist glimpse of paradise would be feasible, according to him, with a simple notational movement "(...) to distinguish between two different kinds of logical operators requires some additional effort. However, this effort is only notational."

This repository contains our implementation of the Ecumenical tableaux for classical and intuitionistic propositional logic on Coq. The system is described in [1].

## Basic notions

Two types of nodes:

1. [Special $\alpha$] Ignore every $F$-signed of its list of predecessors. Is the case of $F_i$ negation and $F_i$ implication.
2. [Special $\beta$] Create checkpoints. Is the case of $F_i$ disjunction.

### Checkpoint

A checkpoint is a record of the tree with a index which indicates the moment it was created.

### State

A state is a complete tree and a list of checkpoints.

### Controller 

The controller is the central component of the implementation. It is responsible for the following:

* It consumes a list of checkpoints; and
* Create a new list of states according to the expansion.

The algorithm stops when there is no more checkpoints to consume.

# Closure 

A tree $\tau$ is closed iff $\tau$ contains $F p$ and $T p$ for some atomic $p$ modulo special $\alpha$ nodes. A tableau is a list of trees.  A tableau is considered closed iff some tree is closed.

# Examples

```
(** P /\ Q |- P **)
Definition inf0 := makeInitialTree
                       Root (((Node true ([P] /\ [Q])))
                               ::((Node false ([P])))
                               ::nil).
Compute closure inf0.
```
```
(** P, P ->i Q |- Q **)
Definition inf2 := makeInitialTree
                       Root (((Node true ([P] ->i [Q])))
                               ::((Node true ([P])))
                               ::((Node false ([Q])))
                               ::nil).
Compute closure inf2.
```
```
(** |/- ((P ->i Q) ->i P) ->i P **)
Definition inf5 := makeInitialTree
                       Root (((Node false ((([P] ->i [Q]) ->i [P]) ->i [P])))
                               ::nil).
Compute closure inf5.
```

# References

[1] Leme, R. R., \& Venturi, G., \& Lopes, B. (2022). Coq Formalization of a Tableau for the Classical-Intuitionistic Propositional Fragment of Ecumenical Logic. WBL (forthcoming).
# Ecumenical tableaux

In ([1](#references)), J.-Y. Girard asks whether is it possible to handle the well-known distinction between "classical" and "intuitionistic" not through a change of system, but through "a change of formulas." While considering different but related thoughts, Krauss figured that, with the adequated ground, such a system would offer a "constructively valid refinement of classical reasoning.'' ([2](#references)) Interestingly enough, this pluralist glimpse of paradise would be feasible, according to him, with a simple notational movement "(...) to distinguish between two different kinds of logical operators requires some additional effort. However, this effort is only notational."

This repository contains our implementation of the Ecumenical tableaux for classical and intuitionistic propositional logic on Coq ([Ecumenical.v](/Ecumenical.v)). The system is described in ([3](#references)).

## Basic notions

Two special types of nodes:

1. **Special $\alpha$**: branch modulo $F$-signed nodes. Is the case of $F_i$ negation and $F_i$ implication.
2. **Special $\beta$**: create checkpoints. Is the case of $F_i$ disjunction.

### Checkpoint

```coq
Inductive checkpoint : Type :=
| null
| Checkpoint : Z -> tree -> checkpoint.
```

A checkpoint is a record of some tree equipped with an index ($i$). This record is a capture of the moment when the rule was applied and the index indicates the location of the respective special $\beta$ node in the tree. The trivial checkpoint is the initial tree with $i=0$.

### State
    
```coq
Inductive state : Type := State : tree -> list checkpoint -> bool -> state.
```

A state is a complete tree plus a list of checkpoints. The boolean is a signal.

### Controller 

The [controller](https://github.com/renatoleme/TEpci_Coq/blob/028359f486b9df7e33fea88afa169e204147fdc8/Ecumenical.v#L542) is the central method of the implementation. It is responsible for the following:

* Consume a list of checkpoints; and
* Create a new list of states according to the expansion.

The algorithm starts with the trivial checkpoint and stops when there are no more checkpoints to consume.

# Closure 

A tree is a set of branches. A branch $S$ is closed iff $S$ contains $F p$ and $T p$ for some atomic $p$ modulo special $\alpha$ nodes. This way, a tree is closed whenever every branch is closed. A tableau, by its turn, is a list of trees; and we will say that a tableau is closed iff some tree of it is closed. The [closure]([/Ecumenical.v#L542](https://github.com/renatoleme/TEpci_Coq/blob/682df55f182e7cc682c7e78db0f8da0bf575c2f9/Ecumenical.v#L667)) function evaluate to true iff the tableau is closed.

# Examples

```coq
(** P /\ Q |- P **)
Definition inf0 := makeInitialTree
                       Root (((Node true ([P] /\ [Q])))
                               ::((Node false ([P])))
                               ::nil).
Compute closure inf0.
```
```coq
(** P, P ->i Q |- Q **)
Definition inf2 := makeInitialTree
                       Root (((Node true ([P] ->i [Q])))
                               ::((Node true ([P])))
                               ::((Node false ([Q])))
                               ::nil).
Compute closure inf2.
```
```coq
(** |/- ((P ->i Q) ->i P) ->i P **)
Definition inf5 := makeInitialTree
                       Root (((Node false ((([P] ->i [Q]) ->i [P]) ->i [P])))
                               ::nil).
Compute closure inf5.
```

# References

[1] Girard, J.-Y.. On the unity of logic. Annals of Pure and Applied Logic, 59, 1993.

[2] Krauss, P.. A Constructive Refinement of Classical Logic. Não publicado, 1992.

[3] Leme, R. R., \& Venturi, G., \& Lopes, B. (2022). Coq Formalization of a Tableau for the Classical-Intuitionistic Propositional Fragment of Ecumenical Logic. WBL (forthcoming).
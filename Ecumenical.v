(*
    A Tableau system for Ecumenical Propositional Logic.
    < coqtop v 8.13.1 >
 *)

Require Import Ascii.
Require Import Bool.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import String.

Module Ecumenical.

  (* Type definitions *)

  Inductive logicalFormula : Set := 
  | Atom   : string -> logicalFormula
  | Neg  : logicalFormula -> logicalFormula
  | And  : (logicalFormula * logicalFormula) -> logicalFormula
  | iOr  : (logicalFormula * logicalFormula) -> logicalFormula
  | cOr  : (logicalFormula * logicalFormula) -> logicalFormula
  | iImp : (logicalFormula * logicalFormula) -> logicalFormula
  | cImp : (logicalFormula * logicalFormula) -> logicalFormula.
  
  Inductive node : Type :=
  | Empty  : node
  | Node : bool -> logicalFormula -> node.
  
  Inductive tree : Type := 
  | Root  : tree
  | Leaf  : tree
  | Unary : tree -> tree -> (bool * (Z*Z) * bool * node) -> tree -> tree
  | Alpha : tree -> tree ->
            ((bool * (Z*Z) * bool * node) * (bool * (Z*Z) * bool * node)) ->
            tree -> tree
  | Beta  : (tree * tree * (bool * (Z*Z) * bool * node) * tree) ->
            (tree * tree * (bool * (Z*Z) * bool * node) * tree) -> tree.

  (* A checkpoint is a snapshot of the current state *)
  Inductive checkpoint : Type :=
  | null
  | Checkpoint : Z -> tree -> checkpoint.
  
  (* A state holds a tableau tree and a list of checkpoints *)
  Inductive state : Type := State : tree -> list checkpoint -> bool -> state.

  Inductive pair : Type := ZZ : (Z * Z) -> pair.

  Inductive prettyTree : Type := 
  | Start : prettyTree
  | End : prettyTree
  | U : (pair * node) -> prettyTree -> prettyTree
  | A : ((pair * node) * (pair * node)) -> prettyTree -> prettyTree
  | B : ((pair * node) * prettyTree) -> ((pair  * node) * prettyTree) -> prettyTree.

  Inductive nodeXTree : Type := nt : Z -> node -> tree -> bool -> nodeXTree.

  Inductive treeXtree : Type := tt : (tree * tree) -> treeXtree.

  (* Notations *)

  Notation "[ A ]"   := (Atom A) (at level 50).
  Notation "~ A"     := (Neg A).
  Notation "A /\ B"  := (And (A, B)).
  Notation "A \/i B" := (iOr (A, B)) (at level 100).
  Notation "A \/c B" := (cOr (A, B)) (at level 100).
  Notation "A ->i B" := (iImp (A, B)) (at level 90).
  Notation "A ->c B" := (cImp (A, B)) (at level 90).

  Notation "@" := (A) (at level 10).
  Notation "#" := (B) (at level 10).
  Notation "$" := (U) (at level 10).

  Notation "p <~ q" := (ZZ (p, q)) (at level 10).

  (* General tools *)

  Fixpoint upto (k : nat) :=
    match k with
    | 0 => nil
    | S n => S n :: upto n 
    end.

  Open Scope Z_scope.

  Fixpoint genTag (tree : tree) := 
    match tree with
    | Root => 0
    | Leaf => 1
    | Unary _ pT (_, (ptag, ctag), lt, l) nT  => ctag + genTag nT
    | Alpha _ pT ((_, (ptagl, ctagl), lt, l), (_, (ptagr, ctagr), rt, r)) nT  =>
        ctagl + ctagr + genTag nT
    | Beta (_, lpT, (_, (ptagl, ctagl), lt, l), lnT) (_, rpT, (_, (ptagr, ctagr), rt, r), rnT) =>
        ctagl + ctagr + genTag lnT + genTag rnT
    end.

  Fixpoint print tree := 
    match tree with
    | Root => Start
    | Leaf => End
    | Unary _ pT (_, (ptag, ctag), lt, l) nT => 
      $ ((ctag <~ ptag), l) (print nT)
    | Alpha _ pT ((_, (ptagl, ctagl), lt, l), (_, (ptagr, ctagr), rt, r)) nT => 
      @ (((ctagl <~ ptagl), l), ((ctagr <~ ptagr), r)) (print nT)
    | Beta (_, lpT, (_, (ptagl, ctagl), lt, l), lnT)
        (_, rpT, (_, (ptagr, ctagr), rt, r), rnT) => 
      # (((ctagl <~ ptagl), l), print lnT) (((ctagr <~ ptagr), r), print rnT)
    end.

  Fixpoint resetTree (tree : tree) :=
    match tree with
    | Root => Root
    | Leaf => Leaf
    | Unary hT pT ((ptag, ctag), t, r) nT => Unary hT pT ((ptag, ctag), true, r) (resetTree nT)
    | Alpha hT pT (((ptagl, ctagl), lt, l), ((ptagr, ctagr), rt, r)) nT => Alpha hT pT (((ptagl, ctagl), true, l), ((ptagr, ctagr), true, r)) (resetTree nT)
    | Beta (lhT, lpT, ((ptagl, ctagl), lt, l), lnT) (rhT, rpT, ((ptagr, ctagr), rt, r), rnT) => 
      Beta (lhT, lpT, ((ptagl, ctagl), true, l), (resetTree lnT)) (rhT, rpT, ((ptagr, ctagr), true, r), (resetTree rnT))
    end.

  Definition pop
    {X : Type}
    (l : list X) default :=
    match l with nil => default | h::tl => h end.
  
  Definition explode
    {X : Type}
    (l : list X) := match l with nil => nil | h::tl => tl end.

  Fixpoint makeInitialTree (prevTree : tree) (nodes : list node) :=
    match nodes with
    | nil => Leaf
    | h::tl => 
        Unary prevTree
          (Unary prevTree prevTree ((true, ((genTag prevTree), (genTag prevTree)), true, h)) Leaf)
          ((true, ((genTag prevTree), (genTag prevTree)), true, h))
          (makeInitialTree
             ((Unary prevTree prevTree ((true, ((genTag prevTree), (genTag prevTree)), true, h)) Leaf))
             tl)
    end.
  
  Definition getPt tree :=
    match tree with
      ( Root | Leaf | Beta _ _ ) => Root
    | Unary _ pT _ _ => pT
    | Alpha _ pT _ _ => pT
    end.

  Definition getHt tree :=
    match tree with
      Root => Root
    | Leaf => Leaf
    | Unary hT pT ((ptag, ctag), t, r) nT => hT
    | Alpha hT pT (((ptagl, ctagl), lt, l), ((ptagr, ctagr), rt, r)) nT => hT
    | Beta (lhT, lpT, ((ptagl, ctagl), lt, l), lnT) (rhT, rpT, ((ptagr, ctagr), rt, r), rnT) => lhT
    end.
  
  Definition getTag tree :=
    match tree with
      ( Root | Leaf | Alpha _ _ _ _ | Beta _ _ ) => 0
    | Unary hT pT (_, (ptag, ctag), t, r) nT => ctag
    end.


  Definition getNt tree :=
    match tree with
      ( Root | Leaf | Beta _ _ ) => Root
    | Unary _ _ _ nT => nT
    | Alpha _ _ _ nT => nT
    end.

  Definition isFalseIntImp (n : node) :=
    match n with
      Node t op =>
      match op with
        _ ->i _ => negb t
      | _ => false
      end
    | _ => false
    end.

  Open Scope Z_scope. 

  (* Functions *)

  Definition getTreeFromNT nxt := match nxt with nt z n t b => t end.
  Definition getNodeFromNT nxt := match nxt with nt z n t b => n end.
  Definition getTagFromNT  nxt := match nxt with nt z n t b => z end.
  Definition getBoolFromNT nxt := match nxt with nt z n t b => b end.

  Definition getTreeLeft treePair  := match treePair with tt (l, r) => l end.
  Definition getTreeRight treePair := match treePair with tt (l, r) => r end.

  Definition getCheckpointListFromState state := match state with State t cl b => cl end.
  Definition getTreeFromState state := match state with State t cl b => t end.
  Definition getBoolFromState state := match state with State t cl b => b end.

  Definition getTreeFromCheckpoint checkpoint :=
    match checkpoint with null => Root | Checkpoint b t => t end.
  Definition getZFromCheckpoint checkpoint :=
    match checkpoint with null => 0 | Checkpoint b t => b end.

  Open Scope Z_scope.
  
  Fixpoint doWeHaveCheckpointAlready (cp : checkpoint) (lcp : list checkpoint) :=
    match lcp with
      nil => false
    | h::tl =>
      let cptag := (getZFromCheckpoint cp) in
      let thtag := (getZFromCheckpoint h) in
      if cptag =? thtag then true else doWeHaveCheckpointAlready cp tl
    end.

  Definition applyRule
    (prevTree : tree)
    (node : node)
    (ctree : tree)
    (tag : Z)
    (gen : Z)
    (selector : bool) :=
    let uP := 
        fun n1 next => 
          (Unary prevTree prevTree (true, (tag, next), true, n1) Leaf) in
    let aP := 
        fun n1 n2 => 
          (Unary prevTree prevTree (true, (tag, (genTag ctree) + gen), true, n1)
             (Unary Root Root (true, (tag, (genTag ctree + 1) + gen), true, n2) Leaf)) in
    let unaryRule := 
        fun an1 => 
          (Unary (uP an1 ((genTag ctree) + gen)) (uP an1 ((genTag ctree) + gen))
             (true, (tag, (genTag ctree) + gen), true, an1) Leaf) in
    let alphaRule := 
        fun an1 an2 => 
          (Alpha (aP an1 an2) (aP an1 an2) ((true, (tag, (genTag ctree) + gen), true, an1),
               (true, (tag, (genTag ctree + 1) + gen) , true, an2)) Leaf) in
    let betaRule := 
        fun bn1 bn2 => 
          (Beta ((uP bn1 ((genTag ctree) + gen)), (uP bn1 ((genTag ctree) + gen)),
               (true, (tag, (genTag ctree) + gen), true, bn1), Leaf)
             ((uP bn2 ((genTag ctree + 1) + gen)), (uP bn2 ((genTag ctree + 1) + gen)),
               (true, (tag, (genTag ctree + 1) + gen), true, bn2), Leaf)) in
    match node with
      Empty => Leaf
    | Node t op =>
      match op with
        Atom _ => Leaf
      | l /\ r => 
        let an1 := (Node true l) in
        let an2 := (Node true r) in 
        let bn1 := (Node false l) in
        let bn2 := (Node false r) in
        if t then alphaRule an1 an2
        else betaRule bn1 bn2
      | l \/c r => 
        let an1 := (Node true (Neg l)) in
        let an2 := (Node true (Neg r)) in 
        let bn1 := (Node false (Neg l)) in
        let bn2 := (Node false (Neg r)) in
        if t then betaRule bn1 bn2
        else alphaRule an1 an2
      | l ->c r => 
        let an1 := (Node true l) in
        let an2 := (Node true (Neg r)) in 
        let bn1 := (Node false l) in
        let bn2 := (Node false (Neg r)) in
        if t then betaRule bn1 bn2
        else alphaRule an1 an2
      | l \/i r => 
        let an1 := (Node false l) in
        let an2 := (Node false r) in 
        let bn1 := (Node true l) in
        let bn2 := (Node true r) in
        if t then betaRule bn1 bn2
        else if selector then unaryRule an1 else unaryRule an2
      | l ->i r => 
        let an1 := (Node true l) in
        let an2 := (Node false r) in 
        let bn1 := (Node false l) in
        let bn2 := (Node true r) in
        if t then betaRule bn1 bn2
        else alphaRule an1 an2
      | ~ r => 
        let an1 := (Node false r) in
        let an2 := (Node true r) in 
        if t then unaryRule an1
        else unaryRule an2
      end
    end.

  Definition specialAlpha (n : node) :=
    match n with
    | Empty => true 
    | Node t op =>
        match op with
        | ~ r => negb t 
        | l ->i r => negb t 
        | _ => false
        end
    end.

  (** Essa função olha para a memória do estado para encontrar o próximo nó a ser expandido.
      Se for especial beta (false or_i), envia um sinal (true).
   **)
  Fixpoint findNodeToExpand (tree : tree) : nodeXTree :=
    match tree with
    | Unary hT pT (b, (ptag, ctag), t, r) nT => 
        if t then
          match r with
          | Empty =>  nt ctag r (Unary hT pT (b, (ptag, ctag), false, r) nT) false
          | Node tv op =>
              match op with 
              | _ \/i _ => nt ctag r (Unary hT pT (b, (ptag, ctag), false, r) nT) (negb tv)
              | _ => nt ctag r (Unary pT pT (b, (ptag, ctag), false, r) nT) false
              end
          end
        else
          let next := (findNodeToExpand pT) in
          nt (getTagFromNT next)
            (getNodeFromNT next)
            (Unary hT nT (b, (ptag, ctag), false, r) (getTreeFromNT next))
            (getBoolFromNT next)
    | _ => nt 0 Empty Leaf false
    end.
  
  Close Scope string_scope.
  
  Fixpoint removeEveryFalseNode (t : tree) : tree :=
    match t with
    | Unary hT pT (b, (ptag, ctag), t, r) nT =>
        match r with
        | Empty => removeEveryFalseNode pT
        | Node bt op =>
            if bt then
              Unary hT (removeEveryFalseNode pT) (b, (ptag, ctag), t, r) nT
            else removeEveryFalseNode pT
        end
    | _ => Root
    end.
    
  Fixpoint findLeaf
    (ltree : tree)
    (iterator : tree)
    (dir : bool)
    (ctrl : bool) :=
    match iterator with
    | Root => State Root (null::nil) true
    | Leaf => State Leaf (null::nil) true
    | Unary hT pT (b, (ptag, ctag), t, r) nT => 
      match nT with
      | Root => State Root (null::nil) true
      | Leaf => 
          let prev := findNodeToExpand pT in
          let checkpoint := Unary hT pT (b, (ptag, ctag), false, r) nT in
          State 
            (Unary ((getHt (getTreeFromNT prev)))
               ((getTreeFromNT prev))
               (b, (ptag, ctag), t, r)
               (applyRule
                  (if (specialAlpha (getNodeFromNT prev)) then removeEveryFalseNode (getTreeFromNT prev)
                   else (getTreeFromNT prev))
                  (getNodeFromNT prev)
                ltree
                (getTagFromNT prev)
                ctag
                ctrl))
          ((Checkpoint ctag checkpoint) :: nil)
          ((getBoolFromNT prev))
      | (Unary _ _ _ _ | Alpha _ _ _ _ | Beta _ _) =>
        let next := (findLeaf ltree nT dir ctrl) in
        State
          (Unary hT pT (b, (ptag, ctag), t, r)
             (getTreeFromState next))
          (( Checkpoint
               (getZFromCheckpoint
                  (pop (getCheckpointListFromState next) null))
               (Unary hT pT (b, (ptag, ctag), t, r)
                  (getTreeFromCheckpoint
                     (pop (getCheckpointListFromState next) null))) :: nil ))
          (getBoolFromState next)
      end
    | Alpha hT pT ((lb, (ptagl, ctagl), lt, l), (rb ,(ptagr, ctagr), rt, r)) nT => 
        match nT with
        | Root => State Root (null::nil) true
        | Leaf => 
            let prev := findNodeToExpand pT in
            let checkpoint := Alpha hT pT ((lb, (ptagl, ctagl), false, l),
                                  (rb, (ptagr, ctagr), false, r)) nT in
            State
              (Alpha 
                 ((getHt (getTreeFromNT prev)))
                 ((getTreeFromNT prev))
                 ((lb, (ptagl, ctagl), lt, l), (rb, (ptagr, ctagr), rt, r)) 
                 (applyRule
                    (if (specialAlpha (getNodeFromNT prev)) then removeEveryFalseNode (getTreeFromNT prev)
                     else (getTreeFromNT prev))
                    (getNodeFromNT prev)
                    ltree
                    (getTagFromNT prev)
                    (ctagl + ctagr)
                    ctrl))
              ((Checkpoint ctagr checkpoint) :: nil)
              ((getBoolFromNT prev))
        | (Unary _ _ _ _ | Alpha _ _ _ _ | Beta _ _) =>
            let next := (findLeaf ltree nT dir ctrl) in
            State
              (Alpha
                 hT pT ((lb, (ptagl, ctagl), lt, l),
                   (rb, (ptagr, ctagr), rt, r)) (getTreeFromState next))
              ((Checkpoint (getZFromCheckpoint (pop (getCheckpointListFromState next) null))
                  (Alpha hT pT ((lb, (ptagl, ctagl), lt, l), (rb, (ptagr, ctagr), rt, r))
                     (getTreeFromCheckpoint
                        (pop (getCheckpointListFromState next) null))) :: nil ))
              (getBoolFromState next)
        end
    | Beta (lhT, lpT, (lb, (ptagl, ctagl), lt, l), lnT)
        (rhT, rpT, (rb, (ptagr, ctagr), rt, r), rnT) =>
        if dir then
          match lnT with
          | Root => State Root (null::nil) true
          | Leaf =>
              let prev := findNodeToExpand lpT in
              let checkpoint := Beta (lhT, lpT, (lb, (ptagl, ctagl), false, l), lnT)
                                  (rhT, rpT, (rb, (ptagr, ctagr), rt, r), rnT) in
              State 
                (Beta 
                   ((getHt (getTreeFromNT prev)),
                     (((getTreeFromNT prev))),
                     (lb, (ptagl, ctagl), lt, l),
                     (applyRule
                        (if (specialAlpha (getNodeFromNT prev)) then removeEveryFalseNode (getTreeFromNT prev)
                         else (getTreeFromNT prev))
                        (getNodeFromNT prev)
                        ltree
                        (getTagFromNT prev)
                        ctagl
                        ctrl))
                   (rhT, rpT, (rb, (ptagr, ctagr), rt, r), rnT))
                ((Checkpoint ctagl checkpoint) :: nil)
                ((getBoolFromNT prev))
          | (Unary _ _ _ _ | Alpha _ _ _ _ | Beta _ _) =>
              let lnext := (findLeaf ltree lnT dir ctrl) in
              let rnext := (findLeaf ltree rnT dir ctrl) in
              State
                (Beta (lhT, lpT, (lb, (ptagl, ctagl), lt, l), (getTreeFromState lnext))
                   (rhT, rpT, (rb, (ptagr, ctagr), rt, r), (getTreeFromState rnext)))
                ((Checkpoint
                    ((getZFromCheckpoint
                        (pop (getCheckpointListFromState lnext) null)))
                    (Beta
                       (lhT, lpT, (lb, (ptagl, ctagl), lt, l),
                         (getTreeFromCheckpoint
                            (pop (getCheckpointListFromState lnext) null)))
                       (rhT, rpT, (rb, (ptagr, ctagr), rt, r),
                         (getTreeFromCheckpoint
                            (pop (getCheckpointListFromState rnext) null)))) :: nil ))
                ((getBoolFromState lnext))
          end
        else
          match rnT with
          | Root => State Root (null::nil) true
          | Leaf => 
              let prev := findNodeToExpand rpT in
              let checkpoint := Beta (lhT, lpT, (lb, (ptagl, ctagl), lt, l), lnT)
                                  (rhT, rpT, (rb, (ptagr, ctagr), false, r), rnT) in
              State
                (Beta 
                   (lhT, lpT, (lb, (ptagl, ctagl), lt, l), lnT) 
                   ((getHt (getTreeFromNT prev)),
                     (((getTreeFromNT prev))),
                     (rb, (ptagr, ctagr), rt, r),
                     (applyRule
                        (if (specialAlpha (getNodeFromNT prev)) then removeEveryFalseNode (getTreeFromNT prev)
                         else (getTreeFromNT prev))
                        (getNodeFromNT prev)
                        ltree
                        (getTagFromNT prev)
                        ctagr
                        ctrl)))
                ((Checkpoint ctagr checkpoint) :: nil)
                ( (getBoolFromNT prev))
          | (Unary _ _ _ _ | Alpha _ _ _ _ | Beta _ _) =>
              let lnext := (findLeaf ltree lnT dir ctrl) in
              let rnext := (findLeaf ltree rnT dir ctrl) in
              State
                (Beta
                   (lhT, lpT, (lb, (ptagl, ctagl), lt, l), (getTreeFromState lnext))
                   (rhT, rpT, (rb, (ptagr, ctagr), rt, r), (getTreeFromState rnext)))
                ((Checkpoint
                    ((getZFromCheckpoint
                        (pop (getCheckpointListFromState rnext) null)))
                    (Beta
                       (lhT, lpT, (lb, (ptagl, ctagl), lt, l),
                         (getTreeFromCheckpoint
                            (pop (getCheckpointListFromState lnext) null)))
                       (rhT, rpT, (rb, (ptagr, ctagr), rt, r),
                         (getTreeFromCheckpoint
                            (pop (getCheckpointListFromState rnext) null)))) :: nil ))
                ((getBoolFromState rnext))
          end
    end.
  
  Definition tableau tree dir ctrl := findLeaf tree tree dir ctrl.
  
  (** 
      makeTableau expande a arvore (up to l)
   **)
  
  Fixpoint makeTableau
    (l : list nat)
    (t : tree)
    (dir : bool)
    (checkpoints : list checkpoint)
    (ctrl : bool)
    : state :=
    match l with
    | nil => State t checkpoints ctrl
    | h::tl =>
        let newstate := (tableau t dir ctrl) in
        let newcp := pop (getCheckpointListFromState newstate) null in
        if (andb (negb (doWeHaveCheckpointAlready newcp checkpoints))
            (getBoolFromState newstate)) (** o sinal enviado por findNodeToExpand chega aqui **)
        then
          makeTableau
            tl
            (getTreeFromState newstate)
            (negb dir)
            (newcp :: checkpoints)
            ctrl
        else
          makeTableau
            tl
            (getTreeFromState newstate)
            (negb dir)
            checkpoints
            ctrl
    end.

  (** A função controller recebe uma lista de checkpoints e retorna uma lista de states.
      Um state é uma arvore de tableau + uma lista de checkpoints. 
      Um checkpoint é uma imagem da arvore de tableau (uma foto do momento em que F-or_i 
      está sendo expandido. **)
  Fixpoint controller
    (l : list nat)
    (checkpoints : list checkpoint) :=
    match checkpoints with
    | nil => nil
    | h::tl =>
        let next := (tableau (getTreeFromCheckpoint h) false false) in
        let nstate := (makeTableau l (getTreeFromState next) true nil true) in
        (nstate) :: (controller l tl)
    end.

  Fixpoint makeNewCheckpointList (l : list state) :=
    match l with
    | nil => nil
    | a::tl => (getCheckpointListFromState a) ++ (makeNewCheckpointList tl)
    end.
  
  Fixpoint getAllTreesFromListState (l : list state) :=
    match l with
    | nil => nil
    | a::tl => (getTreeFromState a) :: (getAllTreesFromListState tl)
    end.

  Fixpoint computeTableau (l : list nat) (lc : list checkpoint) :=
    let control := (controller l lc) in
    let nextlc := makeNewCheckpointList control in 
    match l with
    | nil => nil
    | h::tl =>
        ((getAllTreesFromListState control)) ++ (computeTableau tl nextlc)
    end.
  
  Definition make (t : tree) :=
    let l := (upto 1000) in
    let newstate := (makeTableau l t true nil true) in
    let newcps := (getCheckpointListFromState newstate) in
    (getTreeFromState newstate)::(computeTableau l newcps).
  
  Fixpoint parse (t : tree) (i : list node) : list (list node) := 
    match t with
    | Root => nil
    | Leaf => i::nil
    | Unary _ pT (_, (ptag, ctag), lt, l) nT => 
        let n := l::i in
        parse nT n
    | Alpha _ pT ((_, (ptagl, ctagl), lt, l), (_, (ptagr, ctagr), rt, r)) nT => 
        let n := l::r::i in
        parse nT n
    | Beta (_, lpT, (_, (ptagl, ctagl), lt, l), lnT)
        (_, rpT, (_, (ptagr, ctagr), rt, r), rnT) => 
        let n1 := l::i in
        let n2 := r::i in
        parse lnT n1 ++ parse rnT n2     
    end.

  Fixpoint length {X : Type} (n : list X) :=
    match n with
      nil => 0
    | a::tl => 1 + length tl
    end.

  (** Algoritmo: pega um, olha todos; loop **)
  Fixpoint lookAround (l : list node) (n : node) (s_alpha : bool) :=
    match l with
    | nil => false
    | h::tl =>
        let c_s_alpha := specialAlpha h in
        let isSAlpha := (orb c_s_alpha s_alpha) in
        match n with
        | Empty => lookAround tl n isSAlpha
        | Node t op =>
            match op with
            | Atom P =>
                match h with
                | Empty => lookAround tl n isSAlpha 
                | Node t2 op2 =>
                    if (implb s_alpha t2) then
                      if xorb t t2 then 
                        match op2 with
                        | Atom Q =>
                            if (eqb P Q) then true
                            else lookAround tl n isSAlpha 
                        | _ => lookAround tl n isSAlpha 
                        end
                      else lookAround tl n isSAlpha 
                    else lookAround tl n isSAlpha
                end
            | _ => lookAround tl n isSAlpha
            end
        end
    end.
  
  Fixpoint branchCloses (l : list node) :=
    match l with
    | nil => false
    | h::tl =>
        match h with
        | Empty => branchCloses tl
        | Node t op =>
            match op with
            | (Atom P) => orb (lookAround l h false) (branchCloses tl) 
            | _ => branchCloses tl
            end
        end
    end.

  (** Tree closes iff every branch closes **)
  Fixpoint treeCloses (l : list (list node)) :=
    match l with
    | nil => true
    | h::tl => andb (branchCloses h) (treeCloses tl)
    end.

  Fixpoint someTreeCloses (l : list (list (list node))) :=
    match l with
    | nil => false
    | h::tl => orb (treeCloses h) (someTreeCloses tl)
    end.

  Fixpoint parseTree (l : list tree) :=
    match l with
    | nil => nil
    | h::tl => (parse h nil) :: (parseTree tl)
    end.

  Definition closure (t : tree) : bool :=
    (someTreeCloses (parseTree (make t))).
  
  (* *)

  Open Scope string_scope.
 
  Definition P := "P".
  Definition Q := "Q".
  Definition R := "R".
  Definition S := "S".
  Definition T := "T".
  Definition X := "X".
    
  (** P /\ Q |- P **)
  Definition inf0 := makeInitialTree
                       Root (((Node true ([P] /\ [Q])))
                               ::((Node false ([P])))
                               ::nil).
  Compute closure inf0.

  (** A ordem de expansão importa. **)
  (* |/- P \/c ~P 
     mas 
     |- ~P \/c P
   *)
  Definition inf1 := makeInitialTree
                       Root (((Node false (~[P] \/c [P])))
                               ::nil).
  Compute closure inf1.

  (** P, P ->i Q |- Q **)
  Definition inf2 := makeInitialTree
                       Root (((Node true ([P] ->i [Q])))
                               ::((Node true ([P])))
                               ::((Node false ([Q])))
                               ::nil).
  Compute closure inf2.

  (** P, P ->c Q |/- ~~Q **)
  Definition inf3 := makeInitialTree
                       Root (((Node true ([P] ->c [Q])))
                               ::((Node true ([P])))
                               ::((Node false (~(~([Q])))))
                               ::nil).
  Compute parseTree (make inf3).

  (** |/- P \/i ~P **)
  Definition inf4 := makeInitialTree
                       Root (((Node false ([P] \/i ~[P])))
                               ::nil).
  Compute closure inf4.
  
  (** |/- ((P ->i Q) ->i P) ->i P **)
  Definition inf5 := makeInitialTree
                       Root (((Node false ((([P] ->i [Q]) ->i [P]) ->i [P])))
                               ::nil).
  Compute closure inf5.

  (* ** *)

(* @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ *)
(*                                                                 *)
(* Example 2 : From (PEREIRA; RODRIGUEZ, 2017), section 2, p. 6    *)
(*                                                                 *)
(* @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ *)

(* Initial trees *)

  Definition ex11 := makeInitialTree 
                       Root ((Node false (([P] ->i [Q]) ->i ([P] ->c [Q])))::nil).
  Definition ex12 := makeInitialTree 
                       Root ((Node false ( ( (([P] /\ [Q]) ->i (~(((~[P]) \/c (~[Q])))))
                                             /\ (((~(((~[P]) \/c (~[Q])))) ->i ([P] /\ [Q]))) ) ))::nil).
  Definition ex13 :=  makeInitialTree 
                        Root ((Node false ( (([P] /\ [Q]) ->i (~([P] ->c (~[Q]))))
                                            /\ (((~([P] ->c (~[Q]))) ->i ([P] /\ [Q]))) ))::nil).
  Definition ex14 :=  makeInitialTree 
                        Root ((Node false ( ((~((~[P]) /\ (~[Q]))) ->i ([P] \/c [Q]) )
                                            /\ (([P] \/c [Q]) ->i (~((~[P]) /\ (~[Q]))) ) ) )::nil).
  Definition ex15 :=  makeInitialTree 
                        Root ((Node false ( ((~([P] /\ (~[Q]))) ->i ([P] ->c [Q]))
                                            /\ (([P] ->c [Q]) ->i (~([P] /\ (~[Q])))) ))::nil).
  
  Compute closure ex11.
  Compute closure ex12.
  Compute print (pop (make ex13) _).
  Compute closure ex14.
  Compute closure ex15.
  
  Close Scope Z_scope.
  
End Ecumenical.

Export Ecumenical.

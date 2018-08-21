Add LoadPath "C:/Coq/buffer".
Require Export ProofObjects.

Theorem plus_one_r' : forall n : nat,
    n + 1 = S n.
Proof. apply nat_ind.
       -apply (eq_refl 1).
       -intros n IH. simpl. rewrite IH. apply (eq_refl (S (S n))).
Qed.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.
(* forall P : natlist1 -> Prop, 
   P nnil1 -> forall  (l : natlist1),
   P l -> forall (n : nat) P (nsnoc1 n l) ->  forall m : natlist1 P m. *)
Check natlist1_ind.

Inductive yesno : Type :=
| yes : yesno
| no : yesno.
(* forall P : yesno -> Prop, P yes -> P no -> forall n : yesno, P n *)
Check yesno_ind.

Inductive byntree : Type :=
| bempty : byntree
| bleaf : yesno -> byntree
| nbranch : yesno -> byntree -> byntree -> byntree.
(* forall P : byntree -> Prop, 
   P bempty -> 
   (forall (y : yesno), P bleaf y) ->
   (forall (y2 : yesno) (b1 : byntree), P b1 ->
   forall (b2 : byntree), P b2 -> P (nbranch y2 b1 n2))
   -> forall b : byntree, P b *)
Check byntree_ind.

Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.
(* forall P : ExSet -> Prop,
   (forall (b : bool), P (con1 b)) ->
   (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
   forall e : ExSet, P e *)
Check ExSet_ind.

Inductive tree (X : Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.
(* forall (X : Type) (P : tree X -> Prop),
   (forall a : X, P (leaf X a)) ->
   (forall t1 : tree X, P t1 -> (forall t2 : tree X, P t2 -> P (node X t1 t2))) ->
   forall t : tree X, P t *)
Check tree_ind.

Inductive mytype (X : Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.
(* forall (X : Type) (P : mytype X -> Prop),
   (forall (x : X), P (constr1 X x)) ->
   (forall (n : nat), P (constr2 X n)) ->
   (forall m : mytype X, P m -> (forall n : nat, P (constr3 X m n))) ->
   (forall m : mytype X, P m) *)
Check mytype_ind.
                                 
Inductive foo (X Y : Type) : Type  :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.
(* forall (X Y : Type) (P : foo X Y -> Prop),
   (forall (x : X), P (bar X Y x)) ->
   (forall (y : Y), P (baz X Y y)) ->
   (forall (f : nat -> foo X Y) 
     (forall (n : nat), P (f n)) -> P (quux X Y f)) ->
   forall f2 : foo X Y, P f2 *)
Check foo_ind.

Inductive foo' (X : Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.                                
(* forall (X : Type) (P : foo' X -> Prop),
   (forall (l : list X) (f : foo' X), P f -> P (C1 X l f)) ->
   P (C2 X) -> forall f : foo', P f *)
Check foo'_ind.

Inductive ev' : nat -> Type :=
| ev'_0 : ev' 0
| ev'_SS : forall n : nat, ev' n -> ev' (S (S n)).

(* forall P : (forall n : nat, ev n -> Prop),
   (P 0 ev 0) ->
   (forall (n : nat) (e : ev n),  P n e -> P (S (S n)) (ev_SS n e)) ->
   (forall (n : nat) (e : ev n), P n e) *)
Check ev'_ind.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).
(* forall P : nat -> Prop,
   P 0 ->
   (forall n, ev n -> P n -> P (S (S n))) ->
   forall n, ev n -> P n *)
Check ev_ind.


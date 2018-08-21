
Require Import Coq.Lists.List
               Coq.Sets.Ensembles.

Section R.
Variable  r  : forall a : Type, list a -> list a .
Variable a_star : forall a b, list a -> list b .

Theorem nil_thm : forall a, (r a) nil = nil.
Proof.
  intros. Admitted.
(* "if fixpoints are allowed then theorems hold only when a b are strict" *)

  
Theorem section1_thm : forall (x y : Type) (l : list x),
  a_star x y (r x l) = r y (a_star x y l).
Proof.
  intros. induction l.
  Admitted.
End R.

(* trying to replicate the definition of types as relations described in
   Theorems for Free! Going to define a relation between types and set
   + look into coq sets
   + describe relation between type and set
   + define the operations / relations between types product etc
*)
Section Types_as_Relations.
  Definition rset A := A -> Prop.
  Definition sub_rset {A} (s s': @rset A) := forall x : A, (s x -> s' x).
  Definition relation A B := @rset (A * B).

  Notation "M ':' A '<==>' B" :=
    (exists r : relation A B, sub_rset M r)(at level 60).

  Definition elm_rset {A} (x : A) (s : @rset A) := s x.
  Notation "x '\in' A" := (elm_rset x A)(at level 60).


  Definition ident_rel {A} := forall x : A, (x, x). 


  
 
  
  
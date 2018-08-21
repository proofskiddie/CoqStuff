Require Import Coq.Lists.List.
Import ListNotations.


Record TapeDescription {A : Type} :=
  TD { l : list A; empty : A; headPos : nat }.

Fixpoint nthReplace {A : Type} (n : nat) (repl : A) (l : list A) : list A :=
  match n, l with
  | _, [] => [repl]
  | 1, (x::xs) => repl :: xs
  | n, (x::xs) => x :: nthReplace (n - 1) repl xs                  
  end.

Inductive OneStep {A : Type} : TapeDescription -> TapeDescription -> Prop :=
| RMov : forall tape : TapeDescription,
    headPos tape < length (l tape)
    -> OneStep tape (@TD A (l tape) (empty tape) ((headPos tape) + 1))
| RMovEnd : forall tape : TapeDescription,
    headPos tape = length (l tape)
    -> OneStep tape (@TD A (l tape ++ [empty tape]) (empty tape) ((headPos tape) + 1))
| LMov : forall tape : TapeDescription,
    headPos tape > 0
    -> OneStep tape (@TD A (l tape) (empty tape) ((headPos tape) - 1))
| LMovEnd : forall tape : TapeDescription,
    headPos tape = 0
    -> OneStep tape (@TD A (empty tape :: l tape) (empty tape) ((headPos tape) - 1))
| Repl a : forall tape : TapeDescription,
    (In a (l tape))
    -> OneStep tape
       (@TD A (nthReplace (headPos tape) a (l tape)) (empty tape) (headPos tape))
| ReplNull a : forall tape : TapeDescription,
    (~ In a (l tape))
    -> OneStep tape tape.

Fixpoint Algorithm {A : Type} (l : list (@TapeDescription A)) : Prop :=
  match l with
  | (cons x (cons y xs)) => OneStep x y /\ Algorithm xs
  |  _ => True                                                     
  end.

Definition Derivation {A : Type} (tape : TapeDescription) : Prop :=
  exists l : list TapeDescription, @Algorithm A (l ++ [tape]).

Inductive state : nat -> Set :=
| state0 : state 0
| staten : forall n : nat, state n -> state (n + 1).             

Notation "'q-' n" := (state n)(at level 60).

Inductive command {A : Set} := | L | R | Rep (a : A) : command.

Definition step {A : Set} :=
  (fun n m : nat => q-n -> A -> @command A -> q-m).



  


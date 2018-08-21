Require Import Coq.Lists.List.

(* there are some things to keep in mind when programming in Ltac
   Variable names must be prefixed by a '?' 
Ltac length ls := (* does not work *)
  match ls with
  | nil => O
  | _ :: ls' => S (length ls')
  end.           
 *)

(* constructors must be prefixed by 'constr:' *)
Ltac length ls := (* does not work *)
  match ls with
  | nil => O
  | (_ :: ?ls') => constr:(S (length ls')) (* this is the Gallina length not recursion *)
  end.           

(* the pose tactic extends the proof context with a new variable that is set
   equal to a particular term, could have also have used idtac n to print the 
   result without changing the context*)
Goal False.
  let n := eval simpl in (length ( 1 :: 2 :: 3 :: nil)) in (* only unrolls once *)
  pose n. Abort.

Reset length.

Ltac length ls :=
  match ls with
  | nil => O
  | _ :: ?ls' =>
    let ls'' := length ls' in
    constr:(S ls'')
  end.

(* weird way you have to test Ltac functions *)
Goal False.
  let n := length ( 1 :: 2 :: 3 :: nil ) in
  pose n.
Abort.
(*
Ltac map T f :=
  let rec map' ls :=
      match ls with
      | nil => constr:(@nil T)
      | ?x :: ?ls' =>
        let x' := f x in
          let ls'' := map' ls' in
            constr:(x' :: ls'')
      end in
  map'.
 *)
(*
context[ ] search for a subterm
used in a match statement *)

Ltac map f :=
  match goal with
  | [H : _ |- _ ] => f H
  end.

Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:((x,x))) (1 :: 2 :: 3 :: nil)
in
  pose ls.
Abort.  

Reset length.

(* use of a continuation allows side effects *)
(* this program prints each one step eval *)
Ltac length ls k :=
  idtac ls;
  match ls with
  | nil => k O
  | _ :: ?ls' => length ls' ltac:(fun n => k (S n))
  end.

Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
Abort.
Ltac le_S_star := apply le_n || (apply le_S; le_S_star).
Section RecursiveLtac.
Theorem le_5_25 : 5 <= 25.
Proof.
  le_S_star.
Qed.  
End RecursiveLtac.

Section Primes.
  
  Definition divides (n m : nat) := exists p : nat, p * n = m.

  Hypotheses
    (divides_0 : forall n : nat, divides n 0)
    (divides_plus : forall n m : nat, divides n m -> divides n (n + m))
    (not_divides_plus : forall n m : nat, ~ divides n m -> ~divides n (n+m))
    (not_divides_lt : forall n m : nat, 0 < m -> m < n -> ~ divides n m)
    (not_lt_2_divides : forall n m : nat, n <> 1 -> n < 2 -> 0 < m -> ~divides n m)
    (le_plus_minus : forall n m : nat, le n m -> m = n + (m - n))
    (lt_lt_or_eq : forall n m : nat, n < S m -> n < m \/ n = m).

  Ltac check_not_divides :=
    match goal with
    | [ |- (~divides ?X1 ?X2) ] =>
      cut (X1 <= X2); [ idtac | le_S_star ]; intros Hle;
      rewrite (le_plus_minus _ _ Hle); apply not_divides_plus;
      simpl; clear Hle; check_not_divides
    | [ |- _ ] => apply not_divides_lt; unfold lt; le_S_star
    end.                          
  Theorem three_div_six : ~(divides  7 12).
    Proof.  check_not_divides. Qed.
  Print three_div_six.
End Primes.

Section section_for_cut_example.
  Variable P Q R T : Prop.
  Hypotheses (H : P -> Q)
             (H0 : Q -> R)
             (H1 : (P -> R) -> T -> Q)
             (H2 : (P -> R) -> T).
  Theorem cut_example : Q.
  Proof.
    cut (P -> R). intro H3. apply H1; [ assumption | apply H2; assumption].
    intro. apply H0. apply H. assumption. Qed.
  Print cut_example.  

  Theorem cut_example' : Q.
  Proof. apply H1 in H2; [apply H2 | |];
  intros H3; apply H in H3; apply H0; apply H3. Qed.

  Print cut_example'.
End section_for_cut_example.
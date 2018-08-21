(* Axioms for PA from mendelson intoduction to logic*)
Axiom S1 : forall (x1 x2 x3 : nat), (x1 = x2 -> (x1 = x3 -> x2 = x3)).
Axiom S2 : forall (x1 x2 : nat), (x1 = x2 -> S x1 = S x2).
Axiom S3 : forall (x1 : nat), ~ (0 = S x1).
Axiom S4 : forall (x1 x2 : nat), S x1 = S x2 -> x1 = x2.
Axiom S5 : forall (x1 : nat), x1 + 0 = x1.
Axiom S6 : forall (x1 x2 : nat), x1 + S x2 = S (x1 + x2).
Axiom S7 : forall (x1 : nat), x1 * 0 = 0.
Axiom S8 : forall (x1 x2 : nat), x1 * (S x2) = (x1 * x2) + x1.
Notation S9 := nat_ind.

Theorem P3_2_a : forall (t : nat), t = t.
Proof. intros. apply S1 with (x1 := t + 0). apply S5. apply S5. Qed.

Theorem P3_2_b : forall (t r : nat), t = r -> r = t.
Proof. intros. apply S1 with (x1 := t). apply H. apply P3_2_a. Qed.

Theorem P3_2_c : forall(t r s : nat), t = r -> (r = s -> t = s).
Proof. intros. apply S1 with (x1 := r). apply P3_2_b. apply H. apply H0. Qed.

(* tactic for solving forms of transitivity *)
Ltac trans_eq :=
  match goal with
          | [P : ?X = ?Y |- ?X = ?Z ] =>
            match goal with
            | [P1 : ?Y = ?Z |- ?X = ?Z] =>
              try (apply P3_2_c with (r := Y); try apply P; try apply P1)
            end
          | [P : ?X = ?Y |- ?Y = ?Z ] =>
            match goal with
            | [P1 : ?X = ?Z |- ?Y = ?Z] =>
              try (apply S1 with (x1 := X); try apply P; try apply P1)
            end
  end.

Ltac blah A B C D :=
  match constr:((A,B,C,D)) with
  | True => idtac
  end.

Goal False.
  blah 1 1 3 4.
Theorem P3_2_d : forall (t r s : nat), r = t -> (s = t -> r = s).
  intros. trans_eq.

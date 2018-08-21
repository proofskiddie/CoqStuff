Add LoadPath "C:/Coq/buffer".
Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof. intros n m o p eq1 eq2. rewrite <- eq1. apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m -> (forall (q r : nat), q = r -> [q;o] = [r;p]) -> [n;o] = [m;p].
Proof. intros n m o p eq1 eq2. apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> [n] = [m].
Proof. intros n m eq1 eq2. apply eq2. apply eq1. Qed.

(* using apply before introducing hypotheses may simplify proof *)
Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof. intros eq1. apply eq1. Qed.

(* use symmetry tatic to swap equality, need to sometimes with apply *)
Theorem silly3_firsttty : 
    forall (n : nat), true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. simpl. symmetry. apply H. Qed.

Theorem rev_excercise1 : forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
Proof. intros l l' H. symmetry. rewrite -> H. apply rev_involutive. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]). 
  apply eq1. apply eq2. Qed.

Example trans_eq_excercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof. intros n m o p eq1 eq2. apply trans_eq with m. apply eq2. apply eq1. Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H. inversion H. reflexivity. Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n ; m] = [o ; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity. Qed.


Theorem inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2. inversion H2. reflexivity. Qed. 

Theorem beq_nat_O_1 : forall n,
  beq_nat 0 n = true -> n = 0.
Proof.
  intros n. destruct n as [| n']. intros H. reflexivity. simpl. intros H. inversion H. Qed. 

(* principle of explosion *)
Theorem inversion_ex6 : forall (X : Type) (x y z : X) (l j : list X), 
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof. intros X x y z l j H1 H2. inversion H1. Qed.

Theorem f_equal : forall (A B : Type) (f:A->B) (x y : A),
  x = y -> f x = f y.
Proof. intros A B f x y H. rewrite -> H. reflexivity. Qed.

(* can use many tatics in the context instead of the goal
  Usually by adding 'in <hypothesis_name>' after the tatic*)
Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof. intros n m b H. simpl in H. apply H. Qed.

(* apply and apply in are backwards and forwards reasoning resp 
  apply is modus ponens and apply in is like modus ponens but on hypotheses*)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof. intros n eq H. symmetry in H. apply eq in H. symmetry in H. apply H. Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m. 
Proof. intros n. induction n as [| n'].
    - intros [| m']. reflexivity. inversion 1.
    - intros [| m']. inversion 1.
      + intros H. apply f_equal. apply IHn'. 
        rewrite <- plus_n_Sm in H. simpl in H.
        rewrite <- plus_n_Sm in H. 
        inversion H. reflexivity.
Qed.

Theorem double_injective: forall n m, 
  double n = double m -> n = m.
Proof. intros n. induction n as [| n'].
  - simpl. intros m eq. destruct m as [| m'].
    +reflexivity.
    +inversion eq.
  - simpl. intros m eq. destruct m as [| m'].
    +simpl. inversion eq.
    +apply f_equal. apply IHn'. inversion eq. reflexivity. 
Qed.

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof. intros n. induction n as [| n' Hn'].
    - intros [| m'].
      +reflexivity.
      +inversion 1.
    - intros [| m'].
      +inversion 1.
      +intros H. simpl in H. apply Hn' in H. 
       rewrite -> H. reflexivity. 
Qed.

Theorem double_injective' : forall n m,
  double n = double m -> n = m.
Proof. intros n m. induction m as [| m'].
  - simpl. intros eq. destruct n as [| n'].
    +reflexivity.
    +inversion eq.
  -intros eq. destruct n as [| n'].
    +inversion eq.
    +apply f_equal. simpl in eq. Abort.
(*
  The above fails because n must be introduced before m
  so we cannot preform case analysis on n. 
  The induction hypothesis is not general enough
 
  Solution to this problem is to use the 
  generalize dependent tactic
*)

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. (* n and m in context *)
  generalize dependent n. 
  induction m as [| m' Hm'].
    - intros [| n']. reflexivity. inversion 1.
    - intros [| n']. inversion 1. 
      + intros H. apply f_equal. apply Hm'. 
        inversion H. reflexivity.
Qed.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof. intros [n] [m]. simpl. intros H. 
       assert (H' : n = m). { apply beq_nat_true. apply H. }
       rewrite H'. reflexivity.
Qed.

Theorem nth_error_after_last : 
  forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    nth_error l n = None.
Proof. intros n X l. generalize dependent n.
       induction l as [| h t Ht].
       -simpl. reflexivity.
       -intros [| n']. 
        +inversion 1.
        +simpl. intros H. apply Ht. 
         inversion H. reflexivity.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, 
  square (n*m) = square n * square m.
Proof. intros n m. unfold square. rewrite mult_assoc.
       assert (H : n * m * n = n * n * m).
      { rewrite mult_comm. apply mult_assoc. }
      rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(* using unfold *)
Definition bar x :=
  match x with  
  | 0 => 5
  | S _ => 5
  end.
(* cannot progress without using destruct 
   but may not know that match is the problem*)
Fact silly_fact_FAILED : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof. intros m. simpl. (* does nothing *)
Abort. 
(* using unfold allows to see that we are getting
   stuck at a match statement *)
Fact silly_fact : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof. intros m. unfold bar. destruct m; reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof. intros X Y. intros l. induction l as [| hl tl Htl].
       -intros. inversion H. reflexivity.
       -intros [| hl1 tl1] [| hl2 tl2]; intros; inversion H.
        Abort.

(* what goes wrong here? *)
Theorem bool_fn_applied_thrice_FAIL :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct (f b) eqn:H.
  - destruct (f true) eqn:Hf.
    + apply Hf.
    + destruct (f false) eqn:Hff.
      ++ reflexivity.
      ++ (* false = true OH NO! *) Abort.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof. intros f b. destruct b.
      - destruct (f true) eqn:Hf.
        { rewrite -> Hf. apply Hf. }
        { destruct (f false) eqn:Hff.
           + apply Hf.
           + apply Hff. }
      - destruct (f false) eqn:Hf.
        { destruct (f true) eqn:Hff.
           + apply Hff.
           + apply Hf. }
        { rewrite -> Hf.  apply Hf. }
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat n m.
Proof. intros. destruct (beq_nat n m); reflexivity.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.

Proof. intros n m p Hn Hp.
      assert (beq_nat n m = true -> n = m) as Enm.
      { apply beq_nat_true. }
      assert (beq_nat m p = true -> m = p) as Emp.
      { apply beq_nat_true. }
      apply Enm in Hn. apply Emp in Hp. 
      rewrite Hn. rewrite Hp. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem filter_excercise : forall (X : Type) (test : X -> bool)
  (x : X) (l lf : list X), filter test l = x :: lf -> test x = true.
Proof. intros X test x l lf. induction l as [| h t Ht].
        - inversion 1.
        - intros H. unfold filter in H. destruct (test h) eqn:Htest.
          + inversion H. rewrite <- H1. apply Htest.
          + apply Ht in H. apply H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | h :: t => andb (test h) (forallb test t)
  end.

Compute forallb evenb [12;1;4;8].
Compute forallb negb [false; false; false].
Compute forallb oddb [1;3;5;7;9].
Compute forallb negb [false;false].
Compute forallb evenb [0;2;4;5].
Compute forallb (beq_nat 5) [].
(* could define this with orb but this way is faster *)
Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | nil => false
  | h :: t =>
    match (test h) with
    | true => true
    | false => existsb test t
  end.

Compute existsb (beq_nat 5) [0;2;3;6].
Compute existsb (andb true) [true;true;false].
Compute existsb oddb [1;0;0;0;0;3].
Compute existsb evenb [].

Definition existsb' {X : Type} (test : X -> bool) (l : list X) :=
  negb (forallb (fun n => negb (test n)) l).

Theorem existsb_existsb' : 
  forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. intros X test l. induction l as [| h t Ht].
      - reflexivity.
      - simpl. destruct (test h) eqn:Htest; unfold existsb'; simpl; rewrite -> Htest; simpl.
        + reflexivity.
        + rewrite -> Ht. reflexivity.
Qed.






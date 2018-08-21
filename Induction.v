Add LoadPath "C:/Coq/buffer".
Require Export Basics.

Theorem plus_n_O : forall (n : nat), n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof. intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  induction n as [| n' IHn'].
  - intros m. reflexivity. 
  - intros m. simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + reflexivity.
    + simpl. rewrite <- IHm'. simpl. reflexivity.
  - induction m as [| m' IHm'].
    + simpl. rewrite -> IHn'. simpl. reflexivity.
    + simpl. rewrite -> IHn'. simpl. rewrite <- IHm'. simpl.
      rewrite <- IHn'. reflexivity. Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - intros m p. simpl. rewrite -> IHn'. reflexivity. Qed.


Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros m n p. rewrite -> plus_assoc.  
  replace (m + n) with (n + m). rewrite -> plus_assoc. reflexivity. 
  rewrite -> plus_comm.
  reflexivity.
Qed.

Theorem mult_Sn_r : forall n m,
   n * S m = n + n * m.
Proof.
  intros n m. induction n as [| n' Hn' ].
  - reflexivity.
  - simpl. rewrite -> Hn'. rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. 
  induction n as [| n' Hn'].
  - rewrite -> mult_0_r. reflexivity.
  - rewrite -> mult_Sn_r. simpl.
    rewrite -> Hn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm.
    reflexivity. Qed.

Theorem evenb_S : forall n : nat, 
  evenb (S n) = negb (evenb n).
Proof. 
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive.
    reflexivity. Qed.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros n. induction n as [| n' Hn'].
  - reflexivity.
  - simpl. rewrite -> Hn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b as [| b']. 
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p' Hp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> Hp'. reflexivity.
Qed. 

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_n_O. 
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros [ ] [ ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' Hn'].
  -reflexivity.
  -simpl. rewrite -> Hn'. rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' Hn'].
  -reflexivity.
  - simpl. rewrite -> mult_plus_distr_r.
    rewrite -> Hn'. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n' Hn' ].
  -reflexivity.
  -simpl. rewrite -> Hn'. reflexivity.
Qed.







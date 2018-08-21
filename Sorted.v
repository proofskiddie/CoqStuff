
Notation "x :: y" := (cons x y).

Inductive sorted : list nat -> Prop :=
  |Sorted0 : sorted nil
  |Sorted1 : forall (n : nat), sorted (n :: nil)
  |Sorted2 : forall (n p : nat) (l : list nat),
            lt n p -> sorted (p :: l) -> sorted (n :: p :: l).

Theorem sorted369 : sorted(3::6::9::nil).
Proof. apply Sorted2. apply le_S. apply le_S. apply le_n.
       apply Sorted2. apply le_S. apply le_S. apply le_n.
       apply Sorted1.
Qed.

Theorem sorted_inv : forall (z : nat) (l : list nat),
  sorted(z::l) -> sorted(l).
Proof. intros. inversion H.
      - apply Sorted0.
      - apply H3.
Qed.

Fixpoint nb_occ (n : nat) (l : list nat) : nat :=
  match l with
  | nil => 0
  | h :: t => if Nat.eqb h n then 1 + (nb_occ n t) else
                                 (nb_occ n t)
  end.

Inductive same_elem : list nat -> list nat -> Prop :=
  | Same_elem0 : same_elem nil nil
  | Same_elem1 : forall l1 l2 : list nat,
    (forall n : nat, nb_occ n l1 = nb_occ n l2) -> same_elem l1 l2.

Lemma nb_occ_Sn : forall (n m p: nat) (l1 l2 : list nat),
   nb_occ n l1 = nb_occ m l2 -> p + (nb_occ n l1) = p + (nb_occ m l2).
Proof. intros. rewrite -> H. reflexivity. Qed.

Theorem equiv_cons : forall (n : nat) (l1 l2 : list nat),
    same_elem l1 l2 -> same_elem (n::l1) (n::l2).
Proof. intros. inversion H. 
  - apply Same_elem1. intros. simpl. destruct (Nat.eqb n n0).
    reflexivity. reflexivity.
  - apply Same_elem1. simpl. intros. destruct (Nat.eqb n n0).
    + apply nb_occ_Sn with (p := 1). apply H0.
    + apply H0.
Qed.

Theorem equiv_perm : forall (n p : nat) (l1 l2 : list nat),
  same_elem l1 l2 -> same_elem (n::p::l1) (p::n::l2).
Proof. intros. inversion H. 
   - apply Same_elem1. intros. simpl. destruct (Nat.eqb n n0).
      + destruct (Nat.eqb p n0). reflexivity. reflexivity.
      + destruct (Nat.eqb p n0). reflexivity. reflexivity.
   - apply Same_elem1. intros. simpl. destruct (Nat.eqb n n0).
      + destruct (Nat.eqb p n0). apply nb_occ_Sn with (p := 2). apply H0. 
        apply nb_occ_Sn with (p := 1). apply H0.
      + destruct (Nat.eqb p n0). apply nb_occ_Sn with (p := 1). apply H0. apply H0.
Qed.

Fixpoint leb (n m : nat) : bool := 
  match n, m with
  | 0, 0 
  | 0, _ => true
  | _, 0 => false
  | S n', S m' => leb n' m'
  end.

Fixpoint aux (n : nat) (l : list nat) :=
  match l with 
  | nil => n::nil
  | p::l' => if leb n p  then n::p::l' else p::(aux n l')
  end.

Theorem aux_same : forall (n2 : nat) (l1 l2 : list nat),
  same_elem l1 (aux n2 l2) <-> same_elem l1 (n2::l2).
Proof. split. intros. 
    - inversion H. induction l2 as [|h t Ht].
      + rewrite <- H2. apply Same_elem0.
      + 
   
      


Theorem aux_equiv : forall (l : list nat) (n : nat),
  same_elem (aux n l) (n::l).
Proof. intros. apply Same_elem1. intros. induction l as [| h t Ht].
  - reflexivity.
  - 



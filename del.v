Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Peano_dec.
 
Definition FiniteDecidability (N : nat) := forall P : (forall n : nat, n < N -> Prop), (forall n : nat, forall ln : n < N, {P n ln} + {~ P n ln}) -> {forall n : nat, forall ln : n < N, P n ln} + {~ forall n : nat, forall ln : n < N, P n ln}.
 
Definition no_lt_0 (n : nat) : ~ n < 0 :=
  (Gt.gt_not_le (S n) 0
            (Gt.gt_le_S 0 (S n)
               (Lt.lt_le_S 0 (S n) (PeanoNat.Nat.lt_0_succ n)))).
 
Theorem lt_n_lt_sn (m n : nat) (m_lt_n : m < n) : m < (S n).
Proof.
  auto with arith.
Qed.
 
Theorem n_lt_sn (n : nat) : n < (S n).
Proof.
  auto.
Qed.
 
Theorem lt_between (m n : nat) (m_lt_sn : m < S n) (m_nlt_n : ~ m < n) : m = n.
Proof.
  omega.
Qed.
 
Theorem lt_between2 (m n : nat) (m_lt_sn : m < S n) (m_nlt_n : ~ m < n) : n = m.
Proof.
  destruct (lt_between m n).
  auto.
  auto.
  auto.
Qed.
 
Definition fd_0 : FiniteDecidability 0.
Proof.
  intros P P_dec.
  apply left.
  intros n ln.
  set (no_ln := no_lt_0 n).
  destruct (no_ln ln).
Defined.
 
Definition lt_unique (m n : nat) (lt_a lt_b : m < n) : lt_a = lt_b.
Proof.
  apply le_unique.
Defined.
 
Section DependentEqualityType.
  Variable T : Type.
  Variable P : T -> Type.
  Variable Q : forall t : T, P t -> Type.
  Hypothesis p_unique : forall (t : T) (p1 p2 : P t), p1 = p2.
  Variable t1 : T.
  Hypothesis p_t1 : P t1.
  Variable t2 : T.
  Hypothesis p_t2 : P t2.
  Hypothesis t1_eq_t2 : t1 = t2.
  Lemma deT_pt1_eq_pt2 : P t1 = P t2.
  Proof.
    rewrite t1_eq_t2.
    reflexivity.
  Qed.
 
  Theorem deT_leibniz : Q t1 p_t1 = Q t2 p_t2.
  Proof.
    destruct t1_eq_t2.
    assert (p_t1 = p_t2) as p_t1_eq_p_t2.
    auto.
    destruct p_t1_eq_p_t2.
    reflexivity.
  Qed.
End DependentEqualityType.
Section DependentEquality.
  Variable T : Type.
  Variable P : T -> Prop.
  Variable Q : forall t : T, P t -> Prop.
  Hypothesis p_unique : forall (t : T) (p1 p2 : P t), p1 = p2.
  Variable t1 : T.
  Hypothesis p_t1 : P t1.
  Variable t2 : T.
  Hypothesis p_t2 : P t2.
  Hypothesis t1_eq_t2 : t1 = t2.
  Lemma de_pt1_eq_pt2 : P t1 = P t2.
  Proof.
    rewrite t1_eq_t2.
    reflexivity.
  Qed.
 
  Theorem de_leibniz : Q t1 p_t1 = Q t2 p_t2.
  Proof.
    destruct t1_eq_t2.
    assert (p_t1 = p_t2) as p_t1_eq_p_t2.
    auto.
    destruct p_t1_eq_p_t2.
    reflexivity.
  Qed.
End DependentEquality.
 
Theorem fd_sym (N : nat) (P : forall n : nat, n < N -> Prop) (m n : nat) (m_eq_n : m = n) (m_lt_N : m < N) (n_lt_N : n < N) : P m m_lt_N = P n n_lt_N.
Proof.
  apply de_leibniz.
  apply (fun x => lt_unique x N).
  auto.
Qed.
 
(*
 
Pseudo-code:
 
For 0 <= i < N
  If ~ P i Then
    Return False (P has a counter-example for a natural number less than N)
Return True (P is universally quantified for each natural number less than N)
 
*)
 
Definition fd_S_N (N : nat) : FiniteDecidability N -> FiniteDecidability (S N).
Proof.
  intros fd_N.
  intros S_P S_P_dec.
  set (P := fun (n : nat) => fun (n_lt_N : n < N) => S_P n (lt_n_lt_sn n N n_lt_N)).
  assert (forall (n : nat) (ln : n < N), {P n ln} + {~ P n ln}) as P_dec.
  intros n ln.
  apply S_P_dec.
  assert (forall (n : nat) (n_lt_N : n < N) (n_lt_S_N : n < S N), P n n_lt_N = S_P n n_lt_S_N) as P_eq_S_P.
  {
    intros n n_lt_N n_lt_S_N.
    unfold P.
    apply fd_sym.
    reflexivity.
  }
  assert (forall (n : nat) (n_lt_N : n < N) (n_lt_S_N : n < S N), S_P n n_lt_S_N = P n n_lt_N) as S_P_eq_P.
  {
    intros n n_lt_N n_lt_S_N.
    unfold P.
    apply fd_sym.
    reflexivity.
  }
  assert (forall (n : nat) (n_lt_N : n < N) (n_lt_S_N : n < S N), P n n_lt_N -> S_P n n_lt_S_N) as P_implies_S_P.
  {
    intros n n_lt_N n_lt_S_N P_n.
    destruct (P_eq_S_P n n_lt_N n_lt_S_N).
    apply P_n.
  }
  assert (forall (n : nat) (n_lt_N : n < N) (n_lt_S_N : n < S N), S_P n n_lt_S_N -> P n n_lt_N) as S_P_implies_P.
  {
    intros n n_lt_N n_lt_S_N S_P_n.
    destruct (P_eq_S_P n n_lt_N n_lt_S_N).
    apply S_P_n.
  }
  destruct (fd_N P P_dec) as [P_yes | P_no].
  (* forall n, P n *)
  {
    destruct (S_P_dec N (n_lt_sn N)) as [S_P_yes | S_P_no].
    (* S_P N *)
    {
      apply left.
      intros n n_lt_S_N.
      destruct (lt_dec n N) as [n_lt_N | n_nlt_N].
      (* n < N *)
      {
        apply (P_implies_S_P n n_lt_N n_lt_S_N).
        auto.
      }
      (* ~ n < N *)
      {
        destruct (lt_between2 n N n_lt_S_N n_nlt_N).
        assert (n_lt_S_N = n_lt_sn N) as unique.
        {
          apply lt_unique.
        }
        destruct unique.
        auto.
      }
    }
    (* ~ S_P N *)
    {
      apply right.
      intros contrary.
      apply S_P_no.
      apply contrary.
    }
  }
  (* ~ forall n, P n *)
  {
    apply right.
    intros contrary.
    apply P_no.
    intros n n_lt_N.
    apply (S_P_implies_P n n_lt_N (lt_n_lt_sn n N n_lt_N)).
    apply contrary.
  }
Defined.
 
Fixpoint fd_all (N : nat) : FiniteDecidability N.
Proof.
  destruct N as [|N].
  apply fd_0.
  apply (fd_S_N N (fd_all N)).
Defined.
 
Definition RangeNat (N : nat) := {n : nat | n < N}.
Definition fd_existential (N : nat) (P : RangeNat N -> Prop) (P_dec : forall n : RangeNat N, {P n} + {~ P n}) :
  {forall n : RangeNat N, P n} + {~ forall n : RangeNat N, P n}.
Proof.
  set (Q := fun (n : nat) (n_lt_N : n < N) => P (exist (fun m => m < N) n n_lt_N)).
  assert (forall (n : nat) (n_lt_N : n < N), {Q n n_lt_N} + {~ Q n n_lt_N}) as Q_dec.
  intros n n_lt_N.
  apply P_dec.
  destruct (fd_all N Q Q_dec) as [all_yes|all_no].
  apply left.
  intros n.
  destruct n as [m lm].
  apply all_yes.
  apply right.
  intros contrary.
  apply all_no.
  intros m lm.
  apply contrary.
Defined.
 
Section FiniteType.
  Variable T : Type.
  Variable P : T -> Prop.
  Variable P_dec : forall t : T, {P t} + {~ P t}.
  Variable N : nat.
  Variable f : RangeNat N -> T.
  Variable surj_f : forall t : T, {n : RangeNat N | f n = t}.
  Definition fd_t : {forall t : T, P t} + {~ forall t : T, P t}.
  Proof.
    set (Q := fun (n : RangeNat N) => P (f n)).
    assert (forall n : RangeNat N, {Q n} + {~ Q n}) as Q_dec.
    intros n.
    apply P_dec.
    destruct (fd_existential N Q Q_dec) as [all_yes|all_no].
    apply left.
    intros t.
    destruct (surj_f t) as [n n_proof].
    assert (Q n) as Q_n.
    auto.
    assert (t = f n) as n_proof2.
    auto.
    rewrite n_proof2.
    auto.
    apply right.
    intros contrary.
    apply all_no.
    intros n.
    apply contrary.
  Defined.
End FiniteType.
Add LoadPath "C:/Coq/buffer".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Maps.

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.                               
  (* forall P : aexp -> Prop,
     (forall n : P (Anum n)) ->
     (forall a : aexp, P a -> (forall b : aexp, P b ->  (APlus a b))) ->
     (forall a : aexp, P a -> (forall b : aexp, P b -> (AMinus a b))) ->
     (forall a : aexp, P a -> (forall b : aexp, P b -> (AMult a b))) ->
     forall a : exp, P a *)

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.
  (* forall P : bexp -> Prop,
     P BTrue -> P BFalse ->
     (forall a a0 : aexp, P (BEq a a0)) ->
     (forall a a0 : aexp, P (BLe a a0)) ->
     (forall b : bexp, P b -> P (BNot b)) ->
     (forall b : bexp, P b -> forall b0 : bexp, P b0 -> P (BAnd b b0)) ->
     forall b : bexp, P b *)

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a b => aeval a + aeval b
    | AMinus a b => aeval a - aeval b
    | AMult a b => aeval a * aeval b
    end.

  Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a b => beq_nat (aeval a) (aeval b)
  | BLe a b => leb (aeval a) (aeval b)
  | BNot b => negb (beval b)
  | BAnd a b => andb (beval a) (beval b)
  end.                     

  Fixpoint optimize_0plus (a : aexp) : aexp :=
    match a with
    | ANum n =>
      ANum n
    | APlus (ANum 0) e2 =>
      optimize_0plus e2
    | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus :
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.

  Theorem optimize_0plus_sound : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a. induction a.
    -reflexivity.
    -destruct a1.
     +destruct n.
      * apply IHa2.
      * simpl. rewrite <- IHa2. reflexivity.
     +simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
     +simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
     +simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.      
    -simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
    -simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
  Qed.

  Theorem silly1 : forall ae, aeval ae = aeval ae.
  Proof. try reflexivity. Qed.

  Theorem silly2 : forall (P : Prop), P -> P.
  Proof.
    intros P HP.
    try reflexivity.
    apply HP.
  Qed.

  Lemma foo : forall n, leb 0 n = true.
  Proof.
    intros.
    destruct n.
    -simpl. reflexivity.
    -simpl. reflexivity.
  Qed.

  Lemma foo' : forall n, leb 0 n = true.
  Proof.
    intros.
    destruct n; simpl; reflexivity.
  Qed.

  Theorem optimize_0plus_sound' : forall a : aexp,
      aeval (optimize_0plus a) = aeval a.
  Proof. intros a. induction a;
           try ( simpl; rewrite IHa1; rewrite IHa2; reflexivity).
         - reflexivity.
         - destruct a1;
           try (simpl; simpl in IHa1; rewrite IHa1;
                rewrite IHa2; reflexivity).
           + destruct n;
             simpl; rewrite IHa2; reflexivity. Qed.

  Theorem optimize_0plus_sound'' : forall a : aexp,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a;
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
      try reflexivity.
    - destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                        rewrite IHa2; reflexivity).
      +destruct n;
        simpl; rewrite IHa2; reflexivity. Qed.

  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.

  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BEq a b => BEq (optimize_0plus a) (optimize_0plus b)
    | BLe a b => BLe (optimize_0plus a) (optimize_0plus b)
    | b => b
    end.

  Theorem optimize_0plus_b_sound : forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof. intros b.
         induction b;
           try (reflexivity);
           try (simpl; rewrite IHb1; rewrite IHb2; reflexivity);
           try (simpl; repeat rewrite optimize_0plus_sound; reflexivity).
  Qed.

  Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. omega.
  Qed.

  Module aevalR_first_try.
    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum : forall n : nat,
        aevalR (ANum n) n
    | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).

    Notation "e \\ n" := (aevalR e n)
                             (at level 50, left associativity)
                           : type_scope.
  End aevalR_first_try.

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where " e \\ n " := (aevalR e n) : type_scope.

  Theorem aeval_iff_aevalR : forall a n,
      a \\ n <-> aeval a = n.
  Proof. intros a n. split.
         -intros H. induction H.
          +reflexivity.
          +simpl. rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
          +simpl. rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
          +simpl. rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
         -generalize dependent n. induction a;
            simpl; intros; subst; constructor;
            try apply IHa1; try apply IHa2; reflexivity.
          Qed.
  
  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : forall (n0 n1 : nat) (a0 a1 : aexp),
      a0 \\ n0 -> a1 \\ n1 -> bevalR (BEq a0 a1) (beq_nat n0 n1)
  | E_BLe : forall (n0 n1 : nat) (a0 a1 : aexp),
      a0 \\ n0 -> a1 \\ n1 -> bevalR (BLe a0 a1) (leb n0 n1)
  | E_BNot : forall (B : bexp) (b : bool), bevalR B b -> bevalR (BNot B) (negb b)  
  | E_BAnd : forall (B0 B1 : bexp) (b0 b1 : bool),
      bevalR B0 b0 -> bevalR B1 b1 -> bevalR (BAnd B0 B1) (andb b0 b1).
  
  Theorem beval_iff_bevalR : forall (b : bexp) (bv : bool),
      bevalR b bv <-> beval b = bv.
  Proof. intros b bv. split.
         -intros H. induction H;
           try (simpl; reflexivity);
           try (simpl; rewrite aeval_iff_aevalR in H;
                rewrite aeval_iff_aevalR in H0; subst;
                reflexivity);
           try (simpl; subst; reflexivity).
         -intros H. generalize dependent bv. induction b;
            intros; destruct bv;
            try (inversion H; constructor; rewrite aeval_iff_aevalR; reflexivity).
            simpl in H.
          ++replace true with (negb false). apply E_BNot. apply IHb.
           apply negb_true_iff in H. apply H. reflexivity.
          *replace false with (negb true). apply E_BNot. apply IHb.
           simpl in H. apply negb_false_iff in H. apply H. reflexivity.
          *simpl in H. rewrite <- H. apply E_BAnd.
           **apply IHb1. reflexivity.
           **apply IHb2. reflexivity.
          *simpl in H. rewrite <- H. apply E_BAnd.
           **apply IHb1. reflexivity.
           **apply IHb2. reflexivity.
  Qed.

End AExp.

Module aevalR_division.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv: aexp -> aexp -> aexp.

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
  | E_ADiv : forall (a1 a2 : aexp) (n1 n2 n3 : nat),
      a1 \\ n1 -> a2 \\ n2 -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3
                                        
  where " e \\ n " := (aevalR e n) : type_scope.

End aevalR_division.

Module aevalR_extended.

  Reserved Notation "e \\ n" (at level 50, left associativity).

  Inductive aexp : Type :=
  | AAny : aexp
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_AAny : forall (n : nat), AAny \\ n
  | E_ANum : forall (n : nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
                                      
  where " e \\ n " := (aevalR e n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Definition empty_state : state := t_empty 0.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.                   

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2))) = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4)))) = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Notation "'SKIP'" := (CSkip).
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
  | SKIP => st
  | x ::= a1 => t_update st x (aeval st a1)
  | c1 ;; c2 =>
    let st' := ceval_fun_no_while st c1 in
    ceval_fun_no_while st' c2
  | IFB b THEN c1 ELSE c2 FI =>
    if (beval st b)
    then ceval_fun_no_while st c1
    else ceval_fun_no_while st c2
  | WHILE b DO c END =>
    st (* bogus *)
  end.

Reserved Notation "c '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval_funR : com -> state -> state -> Prop :=
| E_Skip : forall s,
    SKIP / s \\ s
| E_Ass : forall st a1 n x,
    aeval st a1 = n ->
    (x ::= a1) / st \\ (t_update st x n)
| E_Seq : forall c1 c2 st st' st'',
    c1 / st \\ st' ->
    c2 / st' \\ st'' ->
    (c1 ;; c2) / st \\ st''
| E_IfTrue : forall c1 c2 b st st',
    c1 / st \\ st' ->
    beval st b = true ->
    IFB b THEN c1 ELSE c2 FI / st \\ st'
| E_IfFalse : forall c1 c2 b st st',
    c2 / st \\ st' ->
    beval st b = false ->
    IFB b THEN c1 ELSE c2 FI/ st \\ st'        
| E_WhileEnd : forall c1 b st,
    beval st b = false ->
    WHILE b DO c1 END / st \\ st
| E_WhileLoop : forall c1 b st st' st'',
    beval st b = true ->
    c1 / st \\ st' ->
    WHILE b DO c1 END / st' \\ st'' ->
    WHILE b DO c1 END / st \\ st''          

    where " c '/' st '\\' st' " := (ceval_funR c st st') : type_scope.

Example ceval_example2 :
  (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
  (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof. apply E_Seq with (st' := (t_update empty_state X 0)).
       apply E_Ass. reflexivity.
       apply E_Seq with (st' := (t_update (t_update empty_state X 0) Y 1)).
       apply E_Ass. reflexivity.
       apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  (Y ::= ANum 0;;
   WHILE (BNot (BEq (AId X) (ANum 0))) DO
         Y ::= APlus (AId Y) (AId X);;
         X ::= AMinus (AId X) (ANum 1)
   END).

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
           t_update (t_update (t_update (t_update (t_update (t_update
           empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof. unfold pup_to_n.
       apply E_Seq with (st' := (t_update (t_update empty_state X 2) Y 0)).
       -apply E_Ass. reflexivity.
       -apply E_WhileLoop with (st' := (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1)).
        reflexivity.
        apply E_Seq with (st' := (t_update (t_update (t_update
                          empty_state X 2) Y 0) Y 2)).
        apply E_Ass. reflexivity. apply E_Ass. reflexivity.
        apply E_WhileLoop with (st' := (t_update (t_update (t_update (t_update (t_update (t_update
                                empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0)).
        reflexivity.
        apply E_Seq with (st' := (t_update (t_update (t_update (t_update (t_update
                          empty_state X 2) Y 0) Y 2) X 1) Y 3)).
        apply E_Ass. reflexivity.
        apply E_Ass. reflexivity.
        apply E_WhileEnd. reflexivity.
Qed.

Theorem ceval_deterministic : forall c st st1 st2,
    c / st \\ st1 ->
    c / st \\ st2 ->
    st1 = st2.
Proof. intros c st st1 st2 E1 E2.
       generalize dependent st2.
       induction E1; intros st2 E2; inversion E2; subst.
       -reflexivity.
       -reflexivity.
       -assert (st' = st'0) as EQ1.
        { apply IHE1_1; assumption. }
        subst st'0.
        apply IHE1_2. assumption.
       -apply IHE1. assumption.
       -rewrite H in H6. inversion H6.
       -rewrite H in H6. inversion H6.
       - apply IHE1. assumption.
       - reflexivity.
       - rewrite H in H2. inversion H2.
       - rewrite H in H4. inversion H4.
       - apply IHE1_1 in H3. rewrite <- H3 in H6.
         apply IHE1_2 in H6. apply H6.
Qed.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).
Theorem plus2_spec : forall st n st',
    st X = n ->
    plus2 / st \\ st' ->
    st' X = n + 2.
Proof. intros st n st' HX Heval. inversion Heval.
       subst. clear Heval. simpl. apply t_update_eq. Qed.

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).
Theorem XtimesYinZ_spec : forall st st' n n',
    st X = n -> st Y = n' ->
    XtimesYinZ / st \\ st' ->
    st' Z = n * n'.
Proof. intros st st' n n' HX HY Heval.
       inversion Heval. subst. simpl. apply t_update_eq.
Qed.

Definition loop : com :=
  WHILE BTrue DO SKIP END.
Theorem loop_never_stops : forall st st',
    ~ (loop / st \\ st').
Proof. intros st st' contra. unfold loop in contra.
       remember(WHILE BTrue DO SKIP END) as loopdef
                eqn:Heqloopdef.
       induction contra; try inversion Heqloopdef.
       +rewrite H1 in H. inversion H.
       +apply IHcontra2. apply Heqloopdef.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP
  | _ ::= _ => true
  | c1 ;; c2
  | IFB _ THEN c1 ELSE c2 FI => andb (no_whiles c1) (no_whiles c2)
  | WHILE _ DO _ END => false
  end.

Inductive no_whilesR : com -> Prop :=
| no_whiles_SKIP : no_whilesR SKIP
| no_whiles_CAss : forall i x, no_whilesR (i ::= x)
| no_whiles_CSeq : forall x1 x2,
    no_whilesR x1 -> no_whilesR x2 -> no_whilesR (x1 ;; x2)
| no_whiles_CIFB :  forall x1 x2,
    no_whilesR x1 -> no_whilesR x2 -> (forall b, no_whilesR (IFB b THEN x1 ELSE x2 FI)).

(* first in front of [ ] notation *)
Theorem no_whiles_eqv :
  forall c, no_whiles c = true <-> no_whilesR c.
Proof. intros c. split; intros H. induction c.
       - apply no_whiles_SKIP.
       - apply no_whiles_CAss.
       - simpl in H. rewrite andb_true_iff in H. destruct H. apply no_whiles_CSeq.
            apply IHc1. apply H. apply IHc2. apply H0.
       - simpl in H. rewrite andb_true_iff in H. destruct H. apply no_whiles_CIFB.
            apply IHc1. apply H. apply IHc2. apply H0.
       - inversion H.
       - induction c; try (simpl; reflexivity).
         * inversion H. subst. apply IHc1 in H2. apply IHc2 in H3.
           simpl. apply andb_true_iff. split. apply H2. apply H3.
         * inversion H. subst. apply IHc1 in H2. apply IHc2 in H4.
           simpl. apply andb_true_iff. split. apply H2. apply H4.
         * inversion H.
Qed.
(*dependent pattern matching / when to use eqn
  Searching for proofs : ctrl-c ctrl-a then ctrl-a
*)
Theorem no_whiles_terminating : forall c, no_whilesR c ->
        (forall s1, (exists s2, c / s1 \\ s2)).
Proof. intros c H. induction H; intros.
       -exists s1. constructor.
       -exists (t_update s1 i (aeval s1 x)). constructor. reflexivity.
       -destruct IHno_whilesR1 with (s1 := s1).
        destruct IHno_whilesR2 with (s1 := x). exists x0.
        apply E_Seq with (st' := x). apply H1. apply H2.
       -destruct (beval s1 b) eqn:?;
        [destruct IHno_whilesR1 with (s1:=s1) | destruct IHno_whilesR2 with (s1:=s1)];
        exists x; [apply E_IfTrue | apply E_IfFalse]; try apply H1; try apply Heqb0.
Qed.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                   : list nat :=
  match prog, stack with
  | SPush n :: t, _  => s_execute st (n :: stack) t
  | SLoad i :: t, _  => s_execute st (st i :: stack) t
  | SPlus :: t, h :: h' :: t' => s_execute st ((h' + h) :: t') t
  | SMinus :: t, h :: h' :: t' => s_execute st ((h' - h) :: t') t
  | SMult :: t, h :: h' :: t' => s_execute st ((h' * h) :: t') t
  | _ , _ => stack
  end.

Example s_execute1 :
  s_execute empty_state []
            [SPush 5; SPush 3; SPush 1; SMinus]
  = [2 ; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
  s_execute (t_update empty_state X 3) [3 ; 4]
            [SPush 4; SLoad X; SMult; SPlus]
  = [15 ; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => SPush n :: nil
  | AId i => SLoad i :: nil
  | APlus a b => (s_compile a) ++ (s_compile b) ++ [SPlus]
  | AMinus a b => (s_compile a) ++ (s_compile b) ++ [SMinus]
  | AMult a b => (s_compile a) ++ (s_compile b) ++ [SMult]                       
  end.

Example s_compile1 :
  s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.
(* this is too hard to prove!
Lemma s_compile_plus : forall (st : state) (a b a' b': aexp) (na nb : list nat),
    s_execute st na (s_compile a) = [aeval st a'] ->
    s_execute st nb (s_compile b) = [aeval st b'] ->
    s_execute st (na ++ nb) (s_compile a ++ s_compile b ++ [SPlus]) = [aeval st (APlus a' b')].
Proof. intros st a b a' b' na nb Ha Hb. 
 *)

Lemma s_execute_args : forall (st : state) (e : aexp) (l : list nat) (p : list sinstr),
    s_execute st l (s_compile e ++ p) =
    s_execute st (s_execute st [] (s_compile e) ++ l) p.
Proof. intros st e. induction e.
       -reflexivity.
       -reflexivity.
       -intros l p. simpl. 


Lemma s_execute_nat : forall (st : state) (e : aexp),
    (exists n : nat, s_execute st [] (s_compile e) = [n]).
Proof. intros st e. induction e as [ n | i | | IHe1 | IHe2];
         [exists n | exists (st i) | | | ]; try reflexivity.
       -
               
Theorem s_compile_correct : forall (st : state) (e : aexp),
    s_execute st [] (s_compile e) = [ aeval st e ].
Proof. intros st e. 
      

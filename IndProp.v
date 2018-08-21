Add LoadPath "C:/Coq/buffer".
Require Export Logic.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof. intros n H. apply (ev_SS (2 + n) (ev_SS n H)). 
Qed.

Theorem ev_double : forall n, ev (double n).
Proof. intros n. induction n as [| n' In'].
  - apply ev_0.
  - simpl. apply ((ev_SS (double n')) In'). 
Qed.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof. intros n E.
  inversion E as [| n' E'].
  -simpl. apply ev_0.
  -simpl. apply E'.
Qed. 

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
 intros n E. inversion E as [| n' E'].
  apply ev_minus2 in E'. simpl in E'. apply E'.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, le n m -> le n (S m).

Notation "m <= n" := (le m n).
End Playground.

Definition lt (n m : nat) := le (S n) m.
Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n : nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. intros n m o H H'. induction H' as [| m' o' IH].
  - apply H.
  - apply le_S. apply IH.
Qed. 

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n' Hn'].
  - apply le_n.
  - apply le_S. apply Hn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H as [| n' m' H'].
  - apply le_n.
  - apply le_S in H'. apply H'.
Qed. 


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply le_trans with (n:=S n).
    + apply le_S. apply le_n.
    + apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction a as [| a' Ha'].
  -apply O_le_n.
  -simpl. apply n_le_m__Sn_le_Sm. apply Ha'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt. intros n1 n2 m H. split.
 + apply le_trans with (m:=S n1) (n:= S (n1 + n2)) (o:=m).
  - apply n_le_m__Sn_le_Sm. apply le_plus_l.
  - apply H.
 + apply le_trans with (m:=S n2) (n:= S (n1 + n2)) (o:=m).
  - apply n_le_m__Sn_le_Sm. rewrite -> plus_comm. apply le_plus_l.
  - apply H.
Qed.

Lemma le_Sn__n : forall n m, le (S n) m -> le n m.
Proof. intros. apply le_trans with (m:=n) (n:=S n) (o:=m).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros n m H. apply le_Sn__n in H.
  apply n_le_m__Sn_le_Sm. apply H.
Qed. 
Search leb.

Lemma leb_Sn_r : forall (n m : nat),
   leb n m = true -> leb n (S m) = true.
Proof. intros n. induction n as [| n' Hn'].
  - intros m H. reflexivity.
  - intros m H. simpl. destruct m as [| m'].
    + inversion H.
    + simpl in H. apply Hn' in H. apply H.
Qed.

Lemma leb_Sn_l : forall (n m : nat),
   leb (S n) m = true -> leb n m = true.
Proof. intros n. induction n as [| n' Hn'].
  - intros m H. reflexivity.
  - intros m H. simpl. destruct m as [| m'].
    + inversion H.
    + simpl in H. apply Hn' in H. apply H.
Qed.

Lemma leb_extended_refl : forall n m, leb n (n + m) = true.
Proof. intros n m. induction n as [| n' Hn'].
  - reflexivity.
  - simpl. apply Hn'.
Qed.

Lemma leb_plus : forall n m, 
  leb n m = true <-> (exists k, n + k = m).
Proof. intros n. induction n as [| n' Hn'].
  - intros m. split. 
    + intros H. exists m. reflexivity.
    + intros H. reflexivity.
  - intros [| m']; split.
    + intros H. inversion H.
    + intros H. inversion H as [x H0]. inversion H0.
    + simpl. intros H. apply Hn' in H. destruct H. exists x. rewrite H. reflexivity.
    + simpl. intros H. inversion H as [x H0]. inversion H0. apply leb_extended_refl.
Qed. 

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m H. apply leb_plus in H. destruct H. rewrite <- H. apply le_plus_l.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> leb n m = true.
Proof. intros n. induction n as [| n' Hn'].
  - intros [| m']. reflexivity. reflexivity.
  - intros [| m'] H. 
    + inversion H.
    + simpl. apply Sn_le_Sm__n_le_m in H. apply Hn' in H.
      apply H.
Qed.

(* there must be an easier way to do this, still 
   I like how this proof feels like a written proof *)
Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof. intros n m o H H'. apply leb_plus in H.
       apply leb_plus in H'. destruct H. destruct H'.
       rewrite <- H0. rewrite <- H. rewrite <- plus_assoc.
       apply leb_extended_refl.
Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof. split. apply leb_complete. apply leb_correct.
Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Theorem R_112 : R 1 1 2.
Proof. apply c3. apply c2. apply c1.
Qed.

Definition fR : nat -> nat -> nat := plus.
Search plus.

Theorem R_equiv_fR : forall n m o, R n m o <-> fR m n = o.
Proof. intros n m o. split.
  - intros H. induction H; unfold fR.
    + reflexivity.
    + unfold fR in IHR. rewrite <- plus_n_Sm.
      rewrite IHR. reflexivity.
    + unfold fR in IHR. simpl. rewrite IHR. reflexivity.
    + unfold fR in IHR. simpl in IHR. rewrite <- plus_n_Sm in IHR.
      inversion IHR. reflexivity.
    + rewrite -> plus_comm. apply IHR.
  - intros H. induction H. 
    + unfold fR. generalize dependent n. induction m as [| m' IHm'].
    ++ induction n as [| n' IHn']. apply c1. apply c2. apply IHn'.
    ++ intros n. simpl. apply c3. apply IHm'.
Qed.

End R.

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ r" := (exp_match s r) (at level 80).


Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.


Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not. intros T s H. inversion H.
Qed.
  
Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H. destruct H.
  - apply (MUnionL _ _). apply H.
  - apply (MUnionR _ _). apply H.
Qed.

Lemma fold_app_distr : forall T (x x0 : list (list T)),
    fold app (x ++ x0) [] = fold app x [] ++ fold app x0 [].
Proof. induction x.
           -reflexivity.
           -simpl. intros. rewrite IHx. apply app_assoc.
Qed.

Lemma In_or : forall T (s : list T) (x x0 : list (list T)),
    In s (x ++ x0) -> In s x \/ In s x0.
Proof. intros. induction x. simpl in H. right. apply H. simpl in H.
       destruct H. left. rewrite H. left. reflexivity. destruct IHx.
       apply H. left. right. apply H0. right. apply H0.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. apply All_In in H. induction ss as [| h t Ht ].
  - simpl. apply MStar0.
  - simpl. simpl in H. destruct H. apply Ht in H0. apply (MStarApp h (fold app t []) re).
    + apply H.
    + apply H0.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof. intros. remember (Star re) as re'. induction H.
       -inversion Heqre'.
       -inversion Heqre'.
       -inversion Heqre'.
       -inversion Heqre'.
       -inversion Heqre'.
       -exists []. intros. split. reflexivity. intros. inversion H.
       -apply IHexp_match2 in Heqre' as HH. destruct HH. destruct H1.
        exists (s1::x). split.
        +simpl. rewrite <- H1. reflexivity.
        +intros. simpl in H3. destruct H3. rewrite <- H3. inversion Heqre'.
         rewrite <- H5. apply H. apply H2. apply H3.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof. split.
  - intros. generalize dependent s1. induction s2.  
    + intros. simpl in H. inversion H. reflexivity.
    + intros. simpl in H. inversion H. apply IHs2 in H4. inversion H3. rewrite H4. reflexivity.
  - intros. rewrite H. generalize dependent s1. induction s2. 
    + intros. simpl. apply MEmpty. 
    + intros. simpl. replace (x :: s2) with ([x] ++ s2). apply MApp. apply MChar. 
      apply IHs2 with (s1 := s2). reflexivity. reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
    - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App r1 r2 => andb (re_not_empty r1) (re_not_empty r2)
  | Union r1 r2 => orb (re_not_empty r1) (re_not_empty r2)
  | Star r => true
  end.


Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros. destruct H. induction  H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    + simpl. rewrite IHexp_match. reflexivity.
    + simpl. rewrite orb_true_iff. right. rewrite IHexp_match. reflexivity.
    + reflexivity.
    + reflexivity.
  - intros. induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. destruct H. apply IHre1 in H. destruct H.
      apply IHre2 in H0. destruct H0. exists (x ++ x0). apply MApp. apply H. apply H0. 
    + simpl in H. apply orb_true_iff in H. destruct H.
      ++ apply IHre1 in H. destruct H. exists x. apply MUnionL. apply H.
      ++ apply IHre2 in H. destruct H. exists x. apply MUnionR. apply H.
    + exists []. apply MStar0.
Qed.


Inductive nostutter {X : Type} : list X -> Prop :=
  | NoStutO : nostutter []
  | NoStutChar : forall c : X, nostutter [c]
  | NoStutApp : forall (c h : X) (l : list X),
      c <> h -> nostutter (h::l) -> nostutter (c::h::l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
Qed.

Example test_nostutter_3: nostutter [5].
  Proof. repeat constructor; apply beq_nat_false; auto. 
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. 
Qed.

Lemma star_app : forall T ( s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof. intros T s1 s2 re H1. remember (Star re) as re'. 
  generalize dependent s2. induction H1.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - intros.  apply H.
  - intros. apply IHexp_match2 in H. rewrite <- app_assoc. apply MStarApp. apply H1_. apply H.
    apply Heqre'.
Qed.

Module Pumping.

  Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with
    | EmptySet => 0
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
    | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
    | Star _ => 1
    end.

  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with
    | 0 => []
    | S n' => l ++ napp n' l
    end.

  Lemma napp_plus : forall T (n m : nat) (l : list T),
      napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l.
    induction n as [| n IHn].
    -reflexivity.
    -simpl. rewrite IHn, app_assoc. reflexivity.
   Qed.

  Lemma pumping : forall T (re : reg_exp T) s,
      s =~ re ->
      pumping_constant re <= length s ->
      exists s1 s2 s3,
        s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.
            Require Import Coq.omega.Omega.
            Proof.
              Admitted. 
End Pumping.

Theorem filter_not_empty_In : forall n l,
    filter (beq_nat n) l <> [] ->
    In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  -simpl. intros H. apply H. reflexivity.
  -simpl. destruct (beq_nat n m) eqn:H.
   + intros _. rewrite beq_nat_true_iff in H. rewrite H.
     left. reflexivity.
   + intros H'.  right. apply IHl'. apply H'.
Qed.

Module FirstTry.

  Inductive reflect : Prop -> bool -> Prop :=
  | ReflectT : forall (P : Prop), P -> reflect P true
  | ReflectF : forall (P : Prop), ~P -> reflect P false.

End FirstTry.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof. intros P b H. destruct b.
       -apply ReflectT. rewrite H. reflexivity.
       -apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof. intros P b H. destruct b; split.
       -intros. reflexivity.
       -intros. inversion H. apply H1.
       -intros. inversion H. apply H1 in H0. inversion H0.
       -intros. inversion H0.
Qed.

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(*this generates n = m (P) and n <> m (~P) as hypothesis directly
  making the proof more streamlined than before *)
Theorem filter_not_empty_In' : forall n l,
    filter (beq_nat n) l <> [] ->
    In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  -simpl. intros H. apply H. reflexivity.
  -simpl. destruct (beq_natP n m) as [H | H].
   +intros _. rewrite H. left. reflexivity.
   +intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
    count n l = 0 -> ~(In n l).
Proof.
  intros n l H. induction l as [| m l' IH].
  -unfold not. intros. inversion H0.
  -simpl in H. destruct (beq_natP n m) in H.
   +inversion H.
   +apply IH in H. unfold not. intros. simpl in H1. destruct H1.
    ++symmetry in H1. apply H0 in H1. inversion H1.
    ++apply H in H1. inversion H1.
Qed.



                                           



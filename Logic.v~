Add LoadPath "C:/Coq/buffer".
Require Export Tatics.
Require Import Coq.Setoids.Setoid.

Check 3 = 3.
Check forall n m : nat, n + m = m + n.
Check forall n : nat, n = n + 1.
Check 3 = 4.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_ture :
  plus_fact.
Proof. reflexivity. Qed.

(* can define function to Prop 
  called parameterized proposition *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

(* functions that return propositions 
define properties of their arguments *)
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(* equality is a function that returns a prop *)
Check @eq.

(* Use split to break up conjunction *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split; reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof. intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_excercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. intros n m H. induction n; induction m.
  - split; reflexivity.
  - split; inversion H. 
  - split; inversion H.
  - split; inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. intros n m H. destruct H as [HA HB].
       rewrite -> HA. rewrite -> HB. reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_excercise in H. destruct H as [HA HB].
  rewrite -> HA. rewrite -> HB. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
 P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof. intros P Q HPQ. destruct HPQ as [HP HQ]. split. apply HQ. apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof. intros P Q R [HP [HQ HR]]. split. split.
       apply HP. apply HQ. apply HR.
Qed.

Lemma or_example :
 forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
    - rewrite -> Hn. reflexivity.
    - rewrite -> Hm. apply mult_comm.
Qed.

Lemma or_intro : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [| n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_eq_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. intros n. induction n as [| n'].
      - intros m H. left. reflexivity.
      - intros [| m] H. 
        + right. reflexivity.
        + inversion H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof. intros P Q [HP | HQ].
        - right. apply HP.
        - left. apply HQ.
Qed.

Module MyNot.
(* this is how Coq defines not *)
Definition not (P : Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall P : Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.

Fact not_implies_our_not : forall P : Prop,
  ~ P -> (forall Q : Prop, P -> Q).
Proof.
  intros P N Q PP. destruct N. apply PP.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.
Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

Theorem not_False :
  ~ False.
Proof. unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. intros P Q [HP HNP]. unfold not in HNP. apply HNP in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof. intros P Q HPiQ HNQ. unfold not. unfold not in HNQ.
       intros HP. apply HPiQ in HP. apply HNQ in HP. destruct HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
~ (P /\ ~P).
Proof. intros P. unfold not. intros CP. destruct CP. apply H0 in H. destruct H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. unfold not in H. apply ex_falso_quodlibet.
  apply H. reflexivity. reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
  intros [] H. unfold not in H. exfalso. apply H.
  reflexivity. reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q: Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
        (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split. apply HBA. apply HAB.
Qed.

Lemma not_true_iff_false : forall b : bool,
  b <> true <-> b = false.
Proof.
  intros b. split.
   -apply not_true_is_false.
   -intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof. intros P; split; intros HP; apply HP.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. intros P Q R PiQ QiR. destruct PiQ. destruct QiR.
       split. 
       - intros HP. apply H in HP. apply H1 in HP. apply HP.
       - intros HP. apply H2 in HP. apply H0 in HP. apply HP.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. intros P Q R. split. intros H. split. 
       - destruct H. left. apply H.
         + destruct H. right. apply H.
       - destruct H. left. apply H. 
         + destruct H. right. apply H0.
       - intros C. destruct C. destruct H.
         + left. apply H.
         + destruct H0. left. apply H0.
           ++ right. split. apply H. apply H0.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_O.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof. intros n [m Hm]. exists(2 + m). apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~(exists x, ~ P x).
Proof. intros X P H. unfold not. intros [x Hx]. apply Hx. apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. intros X P Q. split.
        - intros [x Hx]. destruct Hx.
          + left. exists x. apply H.
          + right. exists x. apply H.
        - intros H. destruct H. 
          + destruct H. exists x. left. apply H.
          + destruct H. exists x. right. apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | h :: t => (h = x) \/ In x t
  end.

Example In_example : In 4 [1; 2; 3; 4; 5].
Proof. simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 : forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof. simpl. intros n [H | [H | []]].
      - exists 1. rewrite <- H. reflexivity.
      - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map : forall (A B : Type) (f : A -> B)
  (l : list A) (x : A),
  In x l ->
  In (f x) (map f l).
Proof. intros A B f l x. induction l as [| h t Ht].
      - intros []. 
      - intros [H1 | H2].
        + rewrite H1. left. reflexivity.
        + right. apply Ht. apply H2.
Qed.

Lemma In_map_iff : forall (A B : Type) (f: A -> B)
  (l : list A) (y : B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof. intros A B f l y. split.
       { induction l as [| h t Ht].
          - intros [].
          - simpl. intros H. destruct H.
            + exists h. split. apply H. left. reflexivity.
            + apply Ht in H. destruct H. exists x.
              destruct H. split. apply H. right. apply H0. }
       { induction l as [| h t Ht].
          - intros [H [M []]].
          - intros [x [Hf HI]]. simpl. simpl in HI. destruct HI. rewrite -> H. left. apply Hf.
            right. apply Ht. exists x. split. apply Hf. apply H. }
Qed.

Lemma In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof. intros A l. split. 
      { induction l as [| h t Ht]; simpl; intros H.
        - right. apply H.
        - destruct H. 
          + left. left. apply H.
          + apply Ht in H. destruct H.
            ++ left. right. apply H.
            ++ right. apply H. }
      {induction l as [| h t Ht ]. intros [H | H'].
          + inversion H.
          + simpl. apply H'.
          + simpl. intros H. destruct H.
            ++ destruct H.
                +++ left. apply H.
                +++ apply or_intro with (B := (In a l')) in H.
                    apply Ht in H. right. apply H.
            ++ apply or_intro with (B := (In a t)) in H. 
                apply or_commut in H. apply Ht in H. right. apply H. }
Qed.

Fixpoint All {A : Type} (P : A -> Prop) (l : list A) : Prop :=
  match l with
  | nil => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In : forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof. intros T P l. split.
- induction l as [| h t Ht]. 
  + simpl. intros H. apply I.
  + intros H. simpl. split.
    ++ apply H. simpl. left. reflexivity.
    ++ apply Ht. intros Hx HI. apply H. right. apply HI.
- intros Hp. induction l as [| h t Ht].
  + simpl. intros x [].
  + simpl. intros x H. destruct H.
    ++ destruct Hp. rewrite <- H. apply H0.
    ++ apply Ht. destruct Hp. apply H1. apply H.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (fun (n : nat) => (oddb n = true -> Podd n) /\ (oddb n = false -> Peven n)).


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof. intros. unfold combine_odd_even.
split. 
-intros Ho. apply H in Ho. apply Ho.
-intros Hp. apply H0 in Hp. apply Hp.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof. intros. unfold combine_odd_even in H. destruct H.
- apply H in H0. apply H0.
Qed.


Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof. intros. unfold combine_odd_even in H. destruct H.
  apply H1 in H0. apply H0.
Qed.

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
  (forall x, f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.


Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma app_cons : forall X (x : X) (l : list X),
  x :: l = [x] ++ l.
Proof. intros. reflexivity. Qed.

Lemma tr_rev_sing : forall X (x : X),
  tr_rev [x] = [x].
Proof. intros. unfold tr_rev. simpl. reflexivity. Qed.

(* the rub *)
Lemma tr_rev_dist : forall X (l1 l2 : list X),
  tr_rev (l1 ++ l2) = tr_rev l2 ++ tr_rev l1.
Proof. intros X l1. induction l1 as [| h t Ht ].
  - intros. unfold tr_rev. simpl. rewrite -> app_nil_r. reflexivity.
  - intros. simpl. destruct l2 as [| h2 t2 ].
    + simpl. rewrite -> app_nil_r. reflexivity.
    + Admitted.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof. intros. apply functional_extensionality. intros x.
       induction x as [| h t Ht].
        - reflexivity.
        - simpl. rewrite <- Ht. rewrite -> app_cons. rewrite (tr_rev_dist _ [h] t).
          rewrite -> tr_rev_sing. reflexivity.
Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof. intros k. induction k as [| k' IHk'].
        - reflexivity.
        - simpl. apply IHk'.
Qed.

Lemma neg_isnegF : forall b, negb b = true -> b = false.
Proof. intros []. 
        + intros H. rewrite <- H. reflexivity.
        + intros H. reflexivity.
Qed.

Lemma neg_isnegT : forall b, negb b = false -> b = true.
Proof. intros []. 
        + intros H. reflexivity.
        + intros H. rewrite <- H. reflexivity.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k else S (double k).
Proof. intros. induction n as [| n' In']. 
        - exists 0. reflexivity.
        - rewrite -> evenb_S. destruct In'.
          destruct (negb (evenb n')) eqn:Hb.
          + apply (neg_isnegF (evenb n') ) in Hb.
            rewrite -> Hb in H. exists (x + 1).
            rewrite <- plus_comm. simpl. rewrite -> H. reflexivity.
          + apply (neg_isnegT (evenb n')) in Hb. 
            rewrite -> Hb in H. exists x.
            simpl. rewrite <- H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof. split.
      - intros H. 
      apply (andb_true_elim1 b1 b2) in H as Hb1.
      apply (andb_true_elim2 b1 b2) in H as Hb2.
      rewrite -> Hb1. rewrite -> Hb2. 
      split. reflexivity. reflexivity.
      - intros H. destruct H. rewrite -> H. rewrite -> H0.
        reflexivity.
Qed.


Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof. split; intros; destruct b1; destruct b2.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - inversion H.
  - reflexivity.
  - reflexivity. 
  - reflexivity.
  - simpl. inversion H. inversion H0. inversion H0.
Qed.

Theorem beq_nat_false_iff : forall x y : nat,
 	 beq_nat x y = false <-> x <> y.
Proof. split; intros.
    	- unfold not. intros. apply beq_nat_true_iff in H0. rewrite H in H0.
     	 inversion H0.
     	- unfold not in H. destruct (beq_nat x y) eqn:T. 
      	 + apply beq_nat_true_iff in T. apply H in T. inversion T.
       	 + reflexivity.
Qed.

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | _ , nil => false
  | nil, _ => false
  | h::t, h'::t' => andb (beq h h') (beq_list beq t t')
  end.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
  (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
  (forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2).
Proof. intros A beq Heq l1. induction l1 as [| h t Ht].
      - split; intros. destruct l2. reflexivity. inversion H. rewrite <- H. reflexivity.
      - destruct l2 as [| h2 t2 ]. 
        + split; intros. inversion H. inversion H.
        + split; intros.
          ++ simpl in H. apply andb_true_iff in H. destruct H. apply Ht in H0. apply Heq in H.
             rewrite -> H. rewrite -> H0. reflexivity.
          ++ inversion H. simpl. apply andb_true_iff. split.
              +++ apply Heq. reflexivity.
              +++ rewrite H2 in Ht. apply Ht with (l2 := t2). reflexivity.
Qed. 

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof. intros X test l. induction l as [| h t Ht].
      - split; intros. simpl. apply I.
        simpl. reflexivity.
      - split; intros.
        ++ simpl. split.
           +++ inversion H. destruct (test h) eqn:T.
               ++++ symmetry. apply H1.
               ++++ reflexivity.
           +++ inversion H. destruct (test h) eqn:T.
               ++++ apply Ht in H1. simpl in H. rewrite T in H. rewrite -> H. apply H1.
               ++++ inversion H1.
        ++ simpl in H. destruct H. simpl. rewrite -> H. apply Ht. apply H0.
Qed.

Definition excluded_middle := forall (P : Prop), P \/ ~P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof. intros P [] H. 
   - left. apply H. reflexivity.
   - right. rewrite H. intros contra. inversion contra.
Qed. 

Theorem restricted_excluded_middle_eq : forall (n m : nat),
 n = m \/ n <> m.
Proof. intros. apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry. apply (beq_nat_true_iff n m).
Qed.

Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~~(P \/ ~ P).
Proof.  intros P H. apply H. right. intros NP. apply H. left. apply NP.
Qed.

Theorem not_exists_dist : 
  excluded_middle -> 
  (forall (X : Type) (P : X -> Prop),
~ (exists x, ~ P x ) -> (forall x, P x)).
Proof. intros E X P H x. unfold excluded_middle in E.
       destruct E with (P := (P x)). 
       - apply H0.
       - destruct H. exists x. apply H0.
Qed.

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_implies_double_neg_elim : excluded_middle -> double_negation_elimination.
unfold excluded_middle. unfold double_negation_elimination.
- intros H P Np. destruct H with (P := P).
  + apply H0.
  + apply Np in H0. inversion H0.
Qed.

Theorem double_neg_elim_implies_peirce : double_negation_elimination -> peirce.
unfold peirce. unfold double_negation_elimination.
- intros H P Q Hp. apply H. intros Np. apply Np in Hp. 
  + inversion Hp.
  + intros. apply Np in H0. inversion H0.
Qed. 

Theorem peirce_implies_implies_to_or : peirce -> implies_to_or.
unfold peirce. unfold  implies_to_or.
- intros H P Q H'. right. apply H with (P:=Q) (Q:=P). intros H''. 
  apply H with (P:=Q) (Q:=~P). intros N. apply N in H'. Admitted.


Theorem implies_to_or_implies_de_morgan_not_and_not : implies_to_or -> de_morgan_not_and_not.
Proof. unfold implies_to_or. unfold de_morgan_not_and_not.
intros. left. Admitted.

Theorem de_morgan_not_and_not_iff_excluded_middle : de_morgan_not_and_not <-> excluded_middle.
unfold de_morgan_not_and_not. unfold excluded_middle.
split. 
-intros H P. apply H with (P := P) (Q := ~P). intros Np. destruct Np. apply H1 in H0. inversion H0.
-intros H P. destruct H with (P := P).
  + intros. left. apply H0.
  + intros. right. destruct H with (P := Q). 
    apply H2. destruct H1. split. apply H0. apply H2.
Qed.


Theorem peirce_iff_excluded_middle : peirce <-> excluded_middle.
Proof. unfold peirce. unfold excluded_middle. split.
-intros H P. Admitted.
Require Import Rbase.
Require Import Rfunctions.
Require Import Ranalysis1.
Require Import RList.
Require Import Classical_Prop.
Require Import Classical_Pred_Type. Open Local Scope R_scope.


Definition included (D1 D2:R -> Prop) : Prop := forall x:R, D1 x -> D2 x.
Definition disc (x:R) (delta:posreal) (y:R) : Prop := Rabs (y - x) < delta.
Definition neighbourhood (V:R -> Prop) (x:R) : Prop :=
  exists delta : posreal, included (disc x delta) V.
Definition open_set (D:R -> Prop) : Prop :=
  forall x:R, D x -> neighbourhood D x.
Definition complementary (D:R -> Prop) (c:R) : Prop := ~ D c.
Definition closed_set (D:R -> Prop) : Prop := open_set (complementary D).
Definition intersection_domain (D1 D2:R -> Prop) (c:R) : Prop := D1 c /\ D2 c.
Definition union_domain (D1 D2:R -> Prop) (c:R) : Prop := D1 c \/ D2 c.
Definition interior (D:R -> Prop) (x:R) : Prop := neighbourhood D x.

Lemma interior_P1 : forall D:R -> Prop, included (interior D) D.
Proof.
  intros. unfold included in |- *. unfold interior in |- *. intros.
    unfold neighbourhood in H. elim H. intros. unfold included in H0.
      apply H0. unfold disc in |- *. unfold Rminus in |- *.
        rewrite Rplus_opp_r. rewrite Rabs_R0. apply (cond_pos x0).
Qed.

Lemma interior_P2 : forall D:R -> Prop, open_set D -> included D (interior D).
Proof.
  intros; unfold open_set in H; unfold included in |- *; intros;
    assert (H1 := H _ H0); unfold interior in |- *; apply H1.
Qed.

Definition point_adherent (D:R -> Prop) (x:R) : Prop :=
  forall V:R -> Prop,
    neighbourhood V x -> exists y : R, intersection_domain V D y.
Definition adherence (D:R -> Prop) (x:R) : Prop := point_adherent D x.

Lemma adherence_P1 : forall D:R -> Prop, included D (adherence D).
Proof.
  intro; unfold included in |- *; intros; unfold adherence in |- *;
    unfold point_adherent in |- *; intros; exists x;
      unfold intersection_domain in |- *; split.
  unfold neighbourhood in H0; elim H0; intros; unfold included in H1; apply H1;
    unfold disc in |- *; unfold Rminus in |- *; rewrite Rplus_opp_r;
      rewrite Rabs_R0; apply (cond_pos x0).
  apply H.
Qed.

Lemma included_trans :
  forall D1 D2 D3:R -> Prop,
    included D1 D2 -> included D2 D3 -> included D1 D3.
Proof.
  unfold included in |- *. intros. apply H0. apply H. apply H1.
Qed.

Lemma interior_P3 : forall D:R -> Prop, open_set (interior D).
Proof.
  intro; unfold open_set, interior in |- *; unfold neighbourhood in |- *;
    intros; elim H; intros.
  exists x0; unfold included in |- *; intros.
  set (del := x0 - Rabs (x - x1)).
  cut (0 < del).
  intro; exists (mkposreal del H2); intros.
  cut (included (disc x1 (mkposreal del H2)) (disc x x0)).
  intro; assert (H5 := included_trans _ _ _ H4 H0).
  apply H5; apply H3.
  unfold included in |- *; unfold disc in |- *; intros.
  apply Rle_lt_trans with (Rabs (x3 - x1) + Rabs (x1 - x)).
  replace (x3 - x) with (x3 - x1 + (x1 - x)); [ apply Rabs_triang | ring ].
  replace (pos x0) with (del + Rabs (x1 - x)).
  do 2 rewrite <- (Rplus_comm (Rabs (x1 - x))); apply Rplus_lt_compat_l;
    apply H4.
  unfold del in |- *; rewrite <- (Rabs_Ropp (x - x1)); rewrite Ropp_minus_distr;
    ring.
  unfold del in |- *; apply Rplus_lt_reg_r with (Rabs (x - x1));
    rewrite Rplus_0_r;
      replace (Rabs (x - x1) + (x0 - Rabs (x - x1))) with (pos x0);
      [ idtac | ring ].
  unfold disc in H1; rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H1.
Qed.


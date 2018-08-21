Add LoadPath "C:/Coq/buffer".
Require Export IndProp.

Definition ev_4' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_8 : ev 8.
Proof. apply (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply (ev_SS (S(S n)) (ev_SS n H)).
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
  (ev_SS (S(S n)) (ev_SS n H)).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  (ev_SS (S(S n)) (ev_SS n H)).

Definition conj_aux' (P Q R : Prop) (PQ : P /\ Q) (QR : Q /\ R) :=
  match PQ, QR with
  | conj HP HQ, conj QH RH => conj HP RH
  end.

Definition conj_fact' : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) => conj_aux' P Q R.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) => fun (PQ : and P Q) => fun (QR : and Q R) =>
                                                match PQ, QR with
                                                | conj HP HQ , conj QH RH => conj HP RH
                                                end.

(* value of A in first case and B in second aprarently brought from the ether, see Theorem or_comm'' below *)
Definition or_comm_aux (P Q : Prop) (H : or P Q) :=
  match H with
  | or_introl P' => or_intror P'
  | or_intror Q' => or_introl Q' 
  end.

Definition or_comm : forall P Q,  P \/ Q -> Q \/ P :=
  fun (P Q: Prop) =>  or_comm_aux P Q.

Definition or_comm' : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) => fun (H : P \/ Q) =>
                        match H with
                        | or_introl P' => or_intror P'
                        | or_intror Q' => or_introl Q'
                        end.
(*at odds with the functional case, A, B have to be explicitly specified, whats the difference?? *)
Theorem or_comm'' : forall P Q, P \/ Q -> Q \/ P.
Proof. intros. destruct H.
       -apply or_intror with (A := Q) in H. apply H.
       -apply or_introl with (B := P) in H. apply H.
Qed.                                    

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 3  (ev_SS 2 (ev_SS 0 ev_0)).

Definition leibniz_equality : forall (X : Type) (x y : X),
    x = y -> (forall (P : X -> Prop), P x -> P y).
               intros. rewrite <- H. apply H0. Defined.

Definition quiz6 : exists x, x + 3 = 4 :=
  ex_intro (fun x => (x + 3) = 4) 1 (eq_refl 4).













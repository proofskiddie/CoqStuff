Inductive term_t : Type :=
| True : term_t
| False : term_t 
| O : term_t
| succ : term_t -> term_t
| pred : term_t -> term_t
| iszero : term_t -> term_t
| if_then_else : term_t -> term_t -> term_t -> term_t.

Notation " ++ x " := (succ x) (at level 60).
Notation " -- x " := (pred x) (at level 60).
Notation "  X ? Y ?? Z " := (if_then_else X Y Z) (at level 80).
Notation " x :: y " := (cons x y) (at level 60, right associativity).
Notation " [ X ; .. ; Y ] " := ( cons X .. (cons Y nil) .. ).
Notation " X ++ Y " := (app X Y).

Module TERM_T.
Fixpoint atom_eq (t1 t2 : term_t) : bool :=
  match t1, t2 with
  | True, True
  | False, False
  | O, O => true
  | _, _ => false
  end.

Fixpoint In_t (x : term_t) (l : list term_t) : bool :=
  match l with
  | nil => false
  | h :: t => 
    match (atom_eq x h) with
    | true => true
    | false => In_t x t
    end
  end.

Fixpoint collapse (l : list term_t) : list term_t :=
 match l with
 | nil => nil
 | h :: t => 
    match (In_t h t) with
    | true => collapse t
    | false => [h] ++ collapse t
    end  
 end.

Fixpoint Const (t : term_t) : list term_t :=
  match t with
  | True => [True]
  | False => [False]
  | O => [O]
  | ++ t' => Const t'
  | -- t' => Const t'
  | iszero t' => Const t'
  | x ? y ?? z => (collapse ((Const x) ++ (Const y) ++ (Const z))) 
  end.

Fixpoint size (t : term_t) : nat :=
  match t with
  | True 
  | False 
  | O => 1
  | ++ t' => 1 + size t'
  | -- t' => 1 + size t'
  | iszero t' => size t'
  | x ? y ?? z => 1 + (size x) + (size y) + (size z)
  end.

Fixpoint depth (t : term_t) : nat :=
  match t with
  | True 
  | False 
  | O => 1
  | ++ t'
  | -- t'
  | iszero t' => 1 + depth t'
  | x ? y ?? z => 1 + (Nat.max (Nat.max (depth x) (depth y)) (depth z))
  end.

Fixpoint length {T} (l : list T) : nat :=
  match l with 
  | nil => 0
  | h :: t => 1 + length t
  end.

Compute (collapse ([True ; False; True])).
Compute (Const (True ? (++ (++ (++ (++ (++ (True ? O ?? (True ? False ?? (++ O)))))))) ?? False)).
Compute (size (True ? (++ (++ (++ (++ (++ (True ? O ?? (True ? False ?? (++ O)))))))) ?? False)).
Compute (depth (True ? (++ (++ (++ (++ (++ (True ? O ?? (True ? False ?? (++ O)))))))) ?? False)).

Lemma plus_comm : forall n m, n + m = m + n.
Proof. induction n; induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
       simpl. rewrite IHn. reflexivity. rewrite <- plus_n_Sm. rewrite IHm. simpl. reflexivity.
Qed. 

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - intros m p. simpl. rewrite -> IHn'. reflexivity. Qed.

Lemma len_distr {T : Type} : forall (t1 t2 : list T),
  length (t1 ++ t2) =
  length t1 + length t2.
Proof. intros t1. induction t1.
    + simpl. reflexivity. 
    + simpl. intros. apply eq_S. apply IHt1.
Qed.

Lemma le_S_l : forall n m, S n <= m -> n <= m.
Proof. intros. induction H. apply le_S. apply le_n.
  apply le_S in IHle. apply IHle.
Qed.

Lemma le_plus_forall : forall n m, n <= m -> (forall r, n <= r + m).
Proof. intros. induction r. apply H. simpl. apply le_S. apply IHr.
Qed.

Lemma le_plus_oth : forall n m, n <= m -> (exists e, e + n = m).
Proof. intros n m H. induction H. exists 0. reflexivity. destruct IHle. exists (S x). 
  apply eq_S in H0. apply H0.
Qed.

Lemma le_oth_plus : forall n m, (exists e, e + n = m) -> n <= m.
Proof. intros n m H. destruct H. generalize dependent n. induction x.
 - intros. rewrite <- H. apply le_n.
 - intros. simpl in H. rewrite -> plus_n_Sm in H. apply IHx in H. apply le_S_l. apply H.
Qed.

Lemma le_plus : forall n1 n2 m1 m2, n1 <= m1 -> n2 <= m2 -> n1 + n2 <= m1 + m2.
Proof. intros. apply le_plus_oth in H. apply le_plus_oth in H0. destruct H. destruct H0.
       apply le_oth_plus. exists (x + x0). 
       assert (HT : x + x0 + (n1 + n2) = (x + n1) + (x0 + n2)).
        { rewrite <- plus_assoc. rewrite (plus_assoc x0 n1 n2). rewrite (plus_comm x0 n1).
          rewrite (plus_assoc x (n1 + x0) n2). rewrite (plus_assoc x n1 x0).
          rewrite (plus_assoc (x + n1) x0 n2). reflexivity.
        }
        rewrite HT. apply f_equal2_plus. apply H. apply H0.
Qed.

Lemma le_trans : forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof. intros. apply le_plus_oth in H. apply le_plus_oth in H0. apply le_oth_plus.
  destruct H. destruct H0. rewrite <- H in H0. exists (x0 + x). rewrite plus_assoc in H0. apply H0.
Qed.

Lemma dist_const : forall t : term_t,
  length (Const t) <= size t.
Proof. intros t. induction t; simpl.
  + apply le_n.
  + apply le_n.
  + apply le_n.
  + apply le_S. apply IHt.
  + apply le_S. apply IHt.
  + apply IHt.
  + assert (Hlen : forall t, length (collapse t) <= length t ).
    { intros. induction t as [| h t' Ht'].
      - simpl. apply le_n.
      - simpl. destruct (collapse t').
        + destruct (In_t h t').
          ++ simpl. apply le_0_n.
          ++ simpl in Ht'. apply le_n_S. apply Ht'.
        + destruct (In_t h t').
          ++ apply le_S. apply Ht'.
          ++ simpl. apply le_n_S. apply Ht'.
    }
    assert (Hdist :
          length (Const t1 ++ Const t2 ++ Const t3) <= size t1 + size t2 + size t3).
    { intros. rewrite (len_distr (Const t1) (Const t2 ++ Const t3)).
       rewrite (len_distr (Const t2) (Const t3)). 
       apply le_plus with (n1 := (length (Const t2))) (m1 := size t2) in IHt3.
       apply le_plus with (n1 := (length (Const t1))) (m1 := size t1) in IHt3. 
       rewrite (plus_assoc (size t1) (size t2) (size t3)) in IHt3. apply IHt3.
       apply IHt1. apply IHt2. }
    - apply le_trans with (n2 := (length (Const t1 ++ Const t2 ++ Const t3))).
      apply Hlen. apply le_S in Hdist. apply Hdist.
Qed.

Fixpoint eval_if_then_else (ev : term_t -> term_t) (t1 : term_t) : term_t :=
  match t1 with 
  | x ? y ?? z => 
      match x with
      | True => y
      | False => z
      | t => ev t ? y ?? z
      end
  | r => r
  end.

Compute (eval_if_then_else (fun x => x) (True ? False ?? False)).
Compute (eval_if_then_else (fun x => x) (True ? (False ? False ?? False) ?? True)).

Definition s := True ? False ?? False.
Definition t := s ? True ?? True.
Definition u := False ? True ?? True.
Example if_t_then_u_derivable : exists ev : term_t -> term_t,
  eval_if_then_else ev (t ? False ?? False) = (u ? False ?? False).
Proof. (exists (eval_if_then_else (eval_if_then_else (fun x => x)))). simpl. reflexivity.
Qed.

(* easy ... perhaps -too- easy *)
(* to easy, if the functions ev are the same then it is trivial. What the theorem is supposted to say
  is that even if there exists different functions it is still determined*)
Theorem Determinancy_of_one_step_eval_if_then_else' : forall (t t1 t2 : term_t) (ev : term_t -> term_t), 
  ((eval_if_then_else ev t = t1)/\ (eval_if_then_else ev t = t2)
  -> t1 = t2).
Proof. intros. destruct H. induction H. apply H0.
Qed.

Definition if_then_derivable t1 t2 := exists (ev : term_t -> term_t), (eval_if_then_else ev t1) = t2.
Notation " x --> y " := (if_then_derivable x y) (at level 80).

(* this isn't true, the eval function needs to be recursivly defined on a restricted type that only 
   includes 'booleans'
Theorem Determinancy_of_one_step_eval_if_then_else : forall t1 t2 t3 : term_t, t1 --> t2 /\ t1 --> t3 -> t2 = t3.
Proof. unfold if_then_derivable. intros. destruct H. destruct H. destruct H0. induction t1.
      + simpl in H. simpl in H0. rewrite <- H. rewrite <- H0. reflexivity.
      + simpl in H. simpl in H0. rewrite <- H. rewrite <- H0. reflexivity.
      + simpl in H. simpl in H0. rewrite <- H. rewrite <- H0. reflexivity.
      + simpl in H. simpl in H0. rewrite <- H. rewrite <- H0. reflexivity.
      + simpl in H. simpl in H0. rewrite <- H. rewrite <- H0. reflexivity.
      + simpl in H. simpl in H0. rewrite <- H. rewrite <- H0. reflexivity.
      + simpl in H. destruct t1_1.
        
Qed. *)
End TERM_T.

Module BOOLEANS.

(* what is the difference between a value and a term in this case
  is there a coherent way to define values of bools as an inductive type?
  I want the value to be the same as if it were of type boolean
*)
Inductive boolean : Type :=
| true : boolean
| false : boolean.

Inductive exp : Type :=
| exp_const : boolean -> exp
| exp_if_then_else : exp -> exp -> exp -> exp.

(* how to define this so that it is 1 step, and makes sense *)
Definition eval_rule_one_step (e : exp) :=
  match e with
  | exp_if_then_else x y z =>
      match x with
      | exp_const true => y
      | exp_const false => z
      | t => t
      end
  | t => t
  end.

End BOOLEANS,



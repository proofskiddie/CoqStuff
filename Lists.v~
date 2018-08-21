Add LoadPath "C:/Coq/buffer".
Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst (p: natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p: natprod) : nat :=
  match p with
  | pair x y => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_paring : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros [n m]. reflexivity. Qed.

Theorem snd_fnd_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros [n m]. reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros [n m]. reflexivity. Qed.


Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Check cons 5 (cons 4 (cons 3 nil)).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Compute mylist.

Notation "x :: l" := (cons x l)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. ( cons y nil) .. ).

Compute [3; 4; 5 ;5].

Fixpoint length ( l : natlist) : nat :=
  match l with
  | [] => 0
  | h :: t => S (length t)
  end.

Fixpoint app (a b : natlist) : natlist :=
  match a with
  | [] => b
  | h :: t => h :: (app t b) 
  end.

Notation "x ++ y" := (app x y)
    (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist := 
  match l with
  | [] => []
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => evenb n'
  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
    match (evenb h) with
    | true => oddmembers t
    | false => h :: oddmembers t
    end
  end.

Fixpoint countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | a, nil => a
  | nil, b => b
  | h :: t, h' :: t' => h :: h' :: (alternate t t')
  end.

Definition bag := natlist.

Fixpoint equal (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', S m' => equal n' m'
  | _, _ => false
  end.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
    match (equal h v) with
    | true => S (count v t)
    | false => count v t
    end  
  end.

Definition sum : bag -> bag -> bag := app.

Definition add (v : nat) (s : bag) : bag := v :: s.

Definition member (v:nat) (s:bag) : bool :=
  match count v s with
  | 0 => false
  | _ => true
  end.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match equal v h with
    | true => t
    | false => h :: (remove_one v t)
    end
  end.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match equal v h with
    | true => remove_all v t
    | false => h :: (remove_all v t)
    end
  end.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1, s2 with
  | nil, nil => true
  | nil, _ => true
  | _ , nil => false
  | h :: t, h' :: t' => 
    match member h s2 with
    | false => false
    | true => (subset t (remove_one h s2)) 
    end
  end.

Theorem app_assoc : forall (l1 l2 l3 : natlist),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' Hl1' ].
  - reflexivity.
  - simpl. rewrite -> Hl1'. reflexivity. Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => (rev t) ++ [h]
  end.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2. induction l1 as [| n l1' Hl1'].
  -reflexivity.
  -simpl. rewrite -> Hl1'. reflexivity.
Qed.


Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' Hl'].
  -reflexivity.
  -simpl. rewrite <- Hl'. rewrite -> app_length.
   simpl. rewrite -> plus_comm. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' Hl'].
  -reflexivity.
  -simpl. rewrite -> Hl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' Hl1'].
  -simpl. rewrite -> app_nil_r. reflexivity.
  -simpl. rewrite -> Hl1'. rewrite -> app_assoc.
   reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' Hl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> Hl'.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. 
  rewrite -> app_assoc. rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' Hl1'].
  - reflexivity.
  - destruct n as [| n'].
    +simpl. rewrite -> Hl1'. reflexivity.
    +simpl. rewrite -> Hl1'. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | _, nil => false
  | nil, _ => false
  | h :: t, h' :: t' => 
    match beq_nat h h' with
    | true => beq_natlist t t'
    | false => false
    end
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.


Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [| n l' Hl'].
  -reflexivity.
  - simpl. rewrite <- beq_nat_refl. rewrite -> Hl'.
    reflexivity.
Qed.

Theorem count_member_nonzero : forall s : bag,
  leb 1 (count 1 (1 :: s)) = true.
Proof. 
  intros s. reflexivity.
Qed.

Lemma ble_n_Sn : forall n : nat,
  leb n (S n) = true.
Proof. intros n. induction n as [| n' Hn'].
  - reflexivity.
  - simpl. rewrite -> Hn'. reflexivity.
Qed.

Theorem remove_decreases_count : forall s : bag,
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [| n s' Hs'].
  - reflexivity.
  - induction n as [| n' Hn'].
    + simpl. rewrite -> ble_n_Sn. reflexivity.
    + simpl. rewrite -> Hs'. reflexivity.
Qed.

Theorem rev_injective : forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H. rewrite <- rev_involutive. 
  rewrite <- H. rewrite -> rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
| Some : nat -> natoption
| None : natoption.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Definition option_elim (d : nat) (opt : natoption) : nat :=
  match opt with
  | None => d
  | Some n => n
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [| n l' Hl'].
  -reflexivity.
  -reflexivity.
Qed.

End NatList.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id (x1 x2 : id) : bool := 
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x : id,
  true = beq_id x x.
Proof.  
  intros [x']. simpl. rewrite <- beq_nat_refl.
  reflexivity. 
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d:partial_map)
                  (x:id) (value:nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq : forall (d:partial_map) (x:id) (v:nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v. simpl. rewrite <- beq_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H. simpl. rewrite -> H. reflexivity.
Qed.
End PartialMap.















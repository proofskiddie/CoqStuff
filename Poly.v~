Add LoadPath "C:/Coq/buffer".
Require Export Lists.

Inductive list (X:Type) : Type :=
  |nil : list X
  |cons : X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Fail Definition mynil := nil.
Compute (@nil nat).


 Notation "x :: l" := (cons x l) 
   (at level 60, right associativity). 
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. ( cons y nil) .. ).

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Notation " l1 ++ l2 " := (app l1 l2).

(*
 Q: why doesnt this add coninual nil to the end of list
 A: app above peels off the nil from the left arg list
*)
Fixpoint rev {X : Type} (l : list X) : list X := 
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Theorem app_nil_r : forall (X:Type) (l : list X),
  l ++ [] = l.
Proof.
  intros X l. induction l as [| n l' Hl'].
  -reflexivity.
  -simpl. rewrite -> Hl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| h l' Hl'].
  -reflexivity.
  -simpl. rewrite -> Hl'. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof. 
  intros X l1 l2. induction l1 as [| n l1' Hl'].
  -reflexivity.
  -simpl. rewrite -> Hl'. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n l1' Hl1' ].
  -simpl. rewrite -> app_nil_r. reflexivity.
  -simpl. rewrite -> Hl1'. rewrite -> app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' Hl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> Hl'.
    reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  |pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "X * Y" := (prod X Y) : type_scope.
Notation "( x , y )" := (pair x y).

Definition fst  {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd  {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | _ , nil => nil
  | nil, _ => nil
  | hx :: tx, hy :: ty => (hx, hy) :: (combine tx ty)  
  end.

Fixpoint split {X Y : Type} (l : list (X * Y))
                : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | h :: t => 
      match (split t) with
      | r => (fst h :: fst r, snd h :: snd r)
      end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n 0 then Some a else nth_error l' (pred n)
  end.

Definition hd_error {X : Type} (l : list X) : option X := 
  match l with
  | nil => None
  | h :: t => Some h
  end.

Definition doit3times {X : Type} (f: X -> X) (n : X) : X :=
  f (f (f  n)).

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | nil => nil
  | a :: l' => if test a then a :: filter test l' else filter test l'
  end.

Compute (fun n => 2 * n) 2.
Compute doit3times (fun n => n * n) 2.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (leb 8 n)) l.


Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;7;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test: X -> bool) (l : list X)
                     : list X * list X :=
  (filter test l, filter (fun n => negb (test n)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Compute partition evenb [1;2;3;4;5;6].

Fixpoint map {X Y : Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | nil => nil
  | h :: t => (f h) :: (map f t)
  end.

Lemma map_distr : forall (X Y : Type) (f : X -> Y) (l1 l2: list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2. induction l1 as [| n' l1' Hl1'].
    -reflexivity.
    -simpl. rewrite -> Hl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| n l' Hl'].
  -reflexivity.
  -simpl. rewrite -> map_distr. rewrite -> Hl'.
   reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X)
                  : (list Y) :=
  match l with
  | nil => nil
  | h :: t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y)
              : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Module Excercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Compute fold_length [1;2;3;4;5].

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof. intros X l. induction l as [| n l' Hl'].
  -reflexivity.
  -simpl. rewrite <- Hl'. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun (x : X) (ly : list Y) => f x :: ly) l nil.

Compute fold_map (fun n => 2 * n) [1;2;3;4].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof. intros X Y f l. induction l as [| n l' Hl'].
  -reflexivity.
  -simpl. rewrite <- Hl'. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
    f (x, y).
Check prod_curry.

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X*Y) : Z :=
    f (fst p) (snd p).
Check prod_uncurry.
Check prod_uncurry (fun (x y : nat) => x + y).

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
   intros X Y Z f x y. reflexivity. Qed. 

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof. intros X Y Z f p. destruct p as (x,y). reflexivity. Qed.


Module Church.
Definition nat := forall (X : Type), (X -> X) -> X -> X.
Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.
Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition three : nat := @doit3times.

Definition succ (n : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Check succ.

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Compute (succ (succ (three)) (list Datatypes.nat) (cons 1) nil).

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) =>
      (n X f (m X f x)).
Compute (plus three three) (list Datatypes.nat) (cons 1) nil.

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition fnat_to_nat (n : nat) : Datatypes.nat :=
  n Datatypes.nat S 0.

(* is there a better way? *)
Definition mult (n m : nat) : nat :=
  fun (X : Type) (f: X -> X) (x : X) =>
       ((fold plus (repeat n (fnat_to_nat m))) zero) X f x.


Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* is there a better way? *)
Definition exp (n m : nat) : nat :=
  fun (X : Type) (f: X -> X) (x : X) =>
       ((fold mult (repeat n (fnat_to_nat m))) one) X f x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.


End Church.
End Excercises.







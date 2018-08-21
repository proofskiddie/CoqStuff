
Notation "[ A ; .. ; B ]" := (cons A ( .. (cons B nil) ..))(at level 70).

Definition const_gn (n : nat) := 7 + 8 * n.
Definition var_gn (n : nat) := 13 + 8 * n.
Definition fun_gn (n m : nat) := 1 + 8 * (Nat.pow 2 n * Nat.pow 3 m).
Definition rel_gn (n m : nat) := 3 + 8 * (Nat.pow 2 n * Nat.pow 3 m).

(* recursive language *)
Inductive Term : Set :=
| Const : (exists n gn, const_gn n = gn) -> Term
| Var : (exists n gn, var_gn n = gn) -> Term
| Func : (exists n m gn, fun_gn n m = gn) -> Term.

Inductive Relation : Set :=
  | Rel : (exists n m gn, rel_gn n m = gn) -> Relation.

Record RecLanguage : Set := L {
  terms : list Term;
  relations : list Relation
}.                        

Ltac constant n :=
  apply Const; exists n; exists (const_gn n); reflexivity.


Ltac variable n :=
  apply Var; exists n; exists (var_gn n); reflexivity.
  

Ltac function n m :=
  apply Func; exists n; exists m; exists (fun_gn n m); reflexivity.


Ltac term n m :=
   try constant n; try variable n; try function n m.

Ltac rel n m :=
  apply Rel; exists n; exists m; exists (rel_gn n m); reflexivity.
  

Section PA.
  Theorem zero : Term. constant 0. Defined.
  Theorem succ : Term. function 1 1. Defined.
  Theorem plus : Term. function 1 2. Defined.
  Theorem mul  : Term. function 2 2. Defined.
  Theorem equality : Relation. rel 1 1. Defined.
  Definition S := L ([zero; succ; plus; mul]) ([equality]).
End PA.

Inductive Formula : Set :=
| Atom : (exists (args : list Term) (n m gn : nat),
             length args = m -> rel_gn n m = gn) -> Formula
| Not : Formula -> Formula                                                      
| Forall : (exists n gn : nat, var_gn n = gn) -> Formula
| Exists : (exists n gn : nat, var_gn n = gn) -> Formula                                  
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula.

Ltac atom n ls :=
  apply Atom; exists ls; exists n; exists (length ls);
  exists (rel_gn n (length ls)); intro; reflexivity.

Ltac formula_forall n := apply Forall; exists n; exists (var_gn n); reflexivity.
Ltac formula_exists n := apply Exists; exists n; exists (var_gn n); reflexivity.

Definition Const_Interp {A : Set} (n : nat) (f : nat -> A) 
  (_ :exists gn, const_gn n = gn) : A := f n.
Definition Var_Interp {A : Set} (n : nat) (f : nat -> A)
  (_ :exists gn, var_gn n = gn) : A := f n.
Definition Func_Interp {A : Set} (n m : nat) (f : nat -> nat -> A)
  (_ :exists gn, fun_gn n m = gn) : A := f n m.
Definition Rel_Interp {A : Set} (n m : nat) (f : nat -> nat -> A -> Prop)
  (_ :exists gn, rel_gn n m = gn) : A -> Prop := f n m.           
Check (Const_Interp _ _).
Record Interpretation : Set := Interp {
  universe : A;
  term_interp : 
  


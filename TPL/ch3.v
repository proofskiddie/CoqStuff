Require Import Coq.Lists.List.

Inductive T : Set :=
 | True  : T
 | False : T
 | IFB : T -> T -> T -> T.

Fixpoint onestep (t : T) : T :=
  match t with
  | IFB True  t2 t3 => t2
  | IFB False t2 t3 => t3
  | IFB (IFB t1 t2 t3) t4 t5 =>
      IFB (IFB (onestep t1) t2 t3) t4 t5
  | t => t
  end.

Inductive onestep_R : T -> T -> Prop :=
  | E_IfTrue (t2 t3 : T) : onestep_R (IFB True t2 t3) t2
  | E_IfFalse (t2 t3 : T) : onestep_R (IFB False t2 t3) t3
  | E_If (t1 t1' t2 t3 : T) : onestep_R t1 t1' -> onestep_R (IFB t1 t2 t3) (IFB t1' t2 t3).

Notation "A --> B" := (onestep_R A B)(at level 60).

Theorem Determinancy_One_Step : forall t t' t'', t --> t' /\ t --> t'' ->  t' = t''.
Proof. intros. destruct H. induction H. Admitted.

Inductive B : Set :=
| BT  : B 
| BF  : B
| BIF : B -> B -> B -> B
| BO  : B
| BS  : B -> B
| BP  : B -> B
| BIZ : B -> B.

(* 
   how to represent a set given a type A
   how to enumerate all values of a given type A
   / represent a set of only constant elements
   
   inductive types in coq have a finite number of constructors. given an 
   evaluation function on a type ( A -> A ) we get a set of values of type A.
   There are two cases to consider for enumerating such values, infinite and finite
   numbers of values. 
   
   given a finite number of constructors all elements of the type can be enumerated.
   this type will be coinductive however. with a finite or infinite number of values
   it is not possible to know when the evaluation function is finished 'visiting' 
   all values. 

   creating a set from an evaluation function. Each time the function is called 
   it will either return a value which is in the set already, is not in the set, or 
   if the evaluation function does not recurse until a value is found, it could return
   a non-value term. 

   Even though in theory all values can be contained in a regular list if there are
   a finite number, it will not be able to actually extract this information from 
   the constructors in the general case. This is becasuse there is no way to tell,
   given an evaluation function and a way of enumerating all elements of a type, 
   when the evaluation function has seen every possible value of the type. 
*)
Section BSet.
  Variable A : Set.
  Definition bset := A -> bool.
  Definition 
End BSet.  

Fixpoint constB (b : B) : list B :=
  match b with
  | BS t 
  | BP t
  | BIZ t => constB t
  | BIF t1 t2 t3 => flat_map constB (t1 :: t2 :: t3 :: nil)
  | x => x :: nil
  end.


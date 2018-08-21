Require Import Coq.Lists.List.
Definition notInList (ls : list nat) :=
  {n : nat | ~(In n ls)}.




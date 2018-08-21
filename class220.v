
Theorem DeMorgan1 : forall A B, negb (andb A B) = orb (negb A) (negb B).
Proof.
  intros. destruct A; destruct B; reflexivity. Qed.

Theorem DeMorgan2 : forall A B, negb (orb A B) = andb (negb A) (negb B).
Proof.
  intros. destruct A; destruct B; reflexivity. Qed.

Check andb.
Check orb.
Print DeMorgan1.
(*DeMorgan1 = 
fun A B : bool =>
if A as b return (negb (b && B) = (negb b || negb B)%bool)
then
 if B as b return (negb (true && b) = (negb true || negb b)%bool)
 then eq_refl
 else eq_refl
else
 if B as b return (negb (false && b) = (negb false || negb b)%bool)
 then eq_refl
 else eq_refl
     : forall A B : bool, negb (A && B) = (negb A || negb B)%bool *)





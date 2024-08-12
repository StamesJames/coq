MyHelloWorld.


IsProjectable 0 0.
IsProjectable S 0.
Definition s := S.
IsProjectable s 0.
Check S.

Inductive Test : (nat->Type) -> nat -> Type :=
| testI : forall (f:(nat->Type)) (n:nat), f n -> forall f (x:nat), Test f n.

IsProjectable testI 2.

Intern S.
Intern (S 0).

IsConstruct S. 
IsConstruct (S 0).
Definition s := S.
IsConstruct s.


MyHelloWorld.
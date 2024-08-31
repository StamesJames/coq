MyHelloWorld.



Inductive Test' : (nat->Type) -> nat -> Type :=
| testI' : forall f n, (f n -> Test' f n).

IsProjectable testI' 2.

Inductive Inner : Type :=
| innerI_nat : forall (x:nat), Inner
| innerI_fun : forall (f:nat->Type), Inner
| innerI_inner : forall (i:Inner), Inner
| innerI_extra : Inner.

Definition inner_proj_x (i:Inner) : option nat :=
match i with 
| innerI_nat x => Some x 
| _ => None
end.

Definition inner_proj_i (i:Inner) : option Inner :=
match i with 
| innerI_inner i => Some i
| _ => None
end.

Definition inner_proj_f (i:Inner) : option (nat->Type) :=
match i with 
| innerI_fun f => Some f
| _ => None
end.

Inductive ExtractTest : Inner -> Inner -> Type :=
| extractTestI : forall (x:nat) (f:nat->Type) (t:f x), ExtractTest (innerI_inner (innerI_nat x)) (innerI_fun f)
| extractTestI_other : forall (x:nat) (f:nat->Type) (t:f x), ExtractTest (innerI_inner (innerI_nat x)) (innerI_fun f)
| extractTestI_extra : forall inner, ExtractTest inner inner
| extractTestI_extra_const: ExtractTest innerI_extra innerI_extra.

Definition proj_extract_test (inner_ix inner_f:Inner) (e:ExtractTest inner_ix inner_f) :
let x := 
    match inner_ix with 
    | innerI_inner inner_x => 
        match inner_x with 
        | innerI_nat x => Some x 
        | _ => None
        end
    | _ => None 
    end in 
let f := 
    match inner_f with 
    | innerI_fun f => Some f
    | _ => None 
    end in
match (x,f) with 
| (Some x, Some f) => option (f x)
| _ => unit
end.
Proof.
destruct e; cbn; try apply tt.
- apply (Some t).
- apply None.
- destruct inner; try apply tt.
    destruct inner; try apply tt.
Defined.

Goal forall x f (t t': f x), extractTestI x f t = extractTestI x f t' -> t = t'.
Proof.
Fail congruence.
intros.
apply (f_equal (proj_extract_test (innerI_inner (innerI_nat x)) (innerI_fun f))) in H.
cbn in H.
congruence.
Qed.

Inductive Inner' : Type :=
| innerI' : forall (T:Type), Inner'.

Inductive ExtractTest' : Inner' -> Type :=
| extractTestI' : forall (x:nat) (f:nat->Type) (t:f x), ExtractTest' (innerI' (f x)).

IsProjectable extractTestI' 2.

Definition proj_extract_test' inner (e:ExtractTest' inner) : 
let T :=
match inner with 
| innerI' T => T
end in 
T
:=
match e with
| extractTestI' x f t => t 
end.

Goal forall x f (t t': f x), extractTestI' x f t = extractTestI' x f t' -> t = t'.
Proof. 
intros.
apply (f_equal (proj_extract_test' (innerI' (f x)))) in H.
cbn in H.
exact H.
Qed.

Inductive Inner'' : nat -> (nat->Type) -> Type :=
| innerI'' : forall (x:nat)(f:nat->Type), Inner'' x f.

Inductive ExtractTest'' : Inner' -> Type :=
| extractTestI'' : forall (x:nat) (f:nat->Type) (t:f x), ExtractTest'' (innerI' (Inner'' x f)).

IsProjectable extractTestI'' 2.

Definition proj_extract_test'' inner (e:ExtractTest'' inner) : Type.

Goal forall x f (t t': f x), extractTestI' x f t = extractTestI' x f t' -> t = t'.
Proof. 
intros.
apply (f_equal (proj_extract_test' (innerI' (f x)))) in H.
cbn in H.
exact H.
Qed.

Definition m := S 0.

Inductive MatchTest : Type :=
| matchTestI : forall (f:(nat->Type)) (n:nat), match m with | 0 => f m | _ => bool end -> MatchTest.

IsProjectable matchTestI 2.


Inductive Test : (nat->Type) -> nat -> Type :=
| testI : forall (f:(nat->Type)) (n:nat), (match n with | 0 => nat | x => bool end) -> forall f (x:nat), Test f n.

IsProjectable testI 2.



IsProjectable 0 0.
IsProjectable S 0.
Definition s := S.
IsProjectable s 0.
Check S.
Definition s' := S.
Goal s = s'.
reflexivity.




Intern S.
Intern (S 0).

IsConstruct S. 
IsConstruct (S 0).
Definition s := S.
IsConstruct s.


MyHelloWorld.
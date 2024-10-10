MyHelloWorld.

(* Axiom (f : bool -> bool).
Axiom (b:bool).

Inductive U : Type :=
  | U_intro (u : bool) : U
  | EMPTY : U.


Definition proj_U (i : U) : option bool :=
  match i with
  | U_intro u => Some u
  | _ => None
  end.

Inductive inner : bool -> Type :=
  | inner_intro u : inner u.

(* we can extract dependencies from the constructed type *)
Inductive wrap : U -> Type :=
  | wrap_intro u : inner (f u) -> wrap (U_intro (f u)).

IsProjectable wrap_intro 1.

  Definition proj_wrap i (v : wrap i) :
  match proj_U i with
  | Some u => inner u
  | None => unit
  end
  :=
  match v with
  | wrap_intro u t => t
  end.
  
Goal forall u v w , wrap_intro u v = wrap_intro u w -> v = w.
Proof.
Fail congruence.
intros.
apply (f_equal (proj_wrap ((U_intro (f u))))) in H.
cbn in H.
exact H.
Qed.



Inductive Test' : (nat->Type) -> nat -> Type :=
| testI' : forall f n, (f n -> Test' f n).

IsProjectable testI' 2. *)

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

Definition proj_extract_test' 
(inner_ix inner_f:Inner) 
(e:ExtractTest inner_ix inner_f)
:
match inner_ix with
| innerI_inner inner_x => 
    match inner_x with 
    | innerI_nat i_x => 
        match inner_f with 
        | innerI_fun i_f => i_f i_x -> i_f i_x
        | _ => unit:Type 
        end
    | _ => unit:Type
    end
| _ => unit:Type
end
.
refine (
    match e with 
    | extractTestI x f t => _
    | _ => _
    end
).
- refine (fun _ => t).
- refine (fun d => d).
- refine (
    match i with
    | 
    )   
refine (
    match inner_ix return 
    ExtractTest inner_ix inner_f -> 
    match inner_ix with
    | innerI_inner inner_x => 
        match inner_x with
        | innerI_nat i_x => 
            match inner_f with 
            | innerI_fun i_f => i_f i_x -> i_f i_x
            | _ => unit:Type 
            end
        | _ => unit:Type
        end
    | _ => unit:Type
    end
    with
    | innerI_inner inner_x => fun e => _ 
    | _ => fun e => tt 
    end e 
).
refine (
    match inner_x return 
    ExtractTest (innerI_inner inner_x) inner_f -> 
    match inner_x with 
    | innerI_nat i_x => 
        match inner_f with 
        | innerI_fun i_f => i_f i_x -> i_f i_x
        | _ => unit:Type 
        end
    | _ => unit:Type
    end
    with
    | innerI_nat i_x => fun e =>  _ 
    | _ => fun e => tt 
    end e
).
refine (
    match inner_f return 
    ExtractTest (innerI_inner (innerI_nat i_x)) inner_f -> 
    match inner_f with 
    | innerI_fun i_f => i_f i_x -> i_f i_x
    | _ => unit:Type 
    end
    with
    | innerI_fun i_f => fun e => _ 
    | _ => fun e => tt 
    end e
).
refine (fun default:i_f i_x => _).
refine (
    match e in ExtractTest (innerI_inner (innerI_nat i_x)) (innerI_fun i_f) with 
    | extractTestI x f t => _ 
    | _ => _
    end
).
-
 
 

Defined.

Goal forall x f (t t': f x), extractTestI x f t = extractTestI x f t' -> t = t'.
Proof.
Fail congruence.
intros.
apply (f_equal (proj_extract_test' (innerI_inner (innerI_nat x)) (innerI_fun f))) in H.
cbn in H.
congruence.
Qed.

Definition proj_extract_test (inner_ix inner_f:Inner) 
(d: 
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
match x with
| Some x => 
    match f with 
    | Some f => (f x)
    | _ => unit
    end
| _ => unit 
end
)
(e:ExtractTest inner_ix inner_f) :
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
match x with
| Some x => 
    match f with 
    | Some f => (f x)
    | _ => unit
    end
| _ => unit 
end.
Proof.
(* refine (
    match e with 
    | extractTestI a b c => c 
    | _ => tt 
    end
). *)
destruct e; cbn.
- apply t.
- apply d.
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
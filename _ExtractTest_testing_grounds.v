MyHelloWorld.

Goal forall x y, S x = S y -> x = y.
Proof.
congruence.
Qed.

Inductive Inner : Type :=
| innerI_nat : forall (x:nat), Inner
| innerI_fun : forall (f:nat->Type), Inner
| innerI_inner : forall (i:Inner), Inner
| innerI_extra : Inner.

Inductive ExtractTest : Inner -> Inner -> Type :=
| extractTestI : forall (x:nat) (f:nat->Type) (t:f x),
    ExtractTest (innerI_inner (innerI_nat x)) (innerI_fun f) 
| extractTestI_other : forall (x:nat) (f:nat->Type) (t:f x), ExtractTest (innerI_inner (innerI_nat x)) (innerI_fun f) 
| extractTestI_extra : forall inner, ExtractTest inner inner
| extractTestI_extra_const: ExtractTest  innerI_extra innerI_extra .

BuildProjectable extractTestI 2.

Definition extract :=
    (fun (i0 i1 : Inner) (e : ExtractTest i0 i1) (d0 : nat -> Type) (d1 : nat) =>
 match
   e in (ExtractTest i i2)
   return
	 (match i2 with
      | innerI_fun f => fun _ : nat -> Type => f
      | _ => fun t : nat -> Type => t
      end d0
        (match i with
         | innerI_inner i3 =>
             match i3 with
             | innerI_nat x => fun _ : nat => x
             | _ => fun t : nat => t
             end
         | _ => fun t : nat => t
         end d1) ->
      match i2 with
      | innerI_fun f => fun _ : nat -> Type => f
      | _ => fun t : nat -> Type => t
      end d0
        (match i with
         | innerI_inner i3 =>
             match i3 with
             | innerI_nat x => fun _ : nat => x
             | _ => fun t : nat => t
             end
         | _ => fun t : nat => t
         end d1))
 with
 | extractTestI x f t =>
     fun
       _ : match innerI_fun f with
           | innerI_fun f0 => fun _ : nat -> Type => f0
           | _ => fun t0 : nat -> Type => t0
           end d0
             (match innerI_inner (innerI_nat x) with
              | innerI_inner i =>
                  match i with
                  | innerI_nat x0 => fun _ : nat => x0
                  | _ => fun t0 : nat => t0
                  end
              | _ => fun t0 : nat => t0
              end d1) =>
     t
 | extractTestI_other x f _ =>
     fun
       H : match innerI_fun f with
           | innerI_fun f0 => fun _ : nat -> Type => f0
           | _ => fun t : nat -> Type => t
           end d0
             (match innerI_inner (innerI_nat x) with
              | innerI_inner i =>
                  match i with
                  | innerI_nat x0 => fun _ : nat => x0
                  | _ => fun t : nat => t
                  end
              | _ => fun t : nat => t
              end d1) =>
     H
 | extractTestI_extra inner =>
     fun
       H : match inner with
           | innerI_fun f => fun _ : nat -> Type => f
           | _ => fun t : nat -> Type => t
           end d0
             (match inner with
              | innerI_inner i =>
                  match i with
                  | innerI_nat x => fun _ : nat => x
                  | _ => fun t : nat => t
                  end
              | _ => fun t : nat => t
              end d1) =>
     H
 | extractTestI_extra_const =>
     fun
       H : match innerI_extra with
           | innerI_fun f => fun _ : nat -> Type => f
           | _ => fun t : nat -> Type => t
           end d0
             (match innerI_extra with
              | innerI_inner i =>
                  match i with
                  | innerI_nat x => fun _ : nat => x
                  | _ => fun t : nat => t
                  end
              | _ => fun t : nat => t
              end d1) =>
     H
 end).

Print extract.

Lemma congruence_test (x : nat) (f : nat -> Type) t1 t2 : extractTestI x f t1 = extractTestI x f t2 -> t1 = t2.
Proof.
congruence.
Qed.
intros E.
apply (f_equal (fun e => extract (innerI_inner (innerI_nat x)) (innerI_fun f) e f x t1)) in E.
cbn in E.
exact E.
Qed.





Definition extract (i0 i1:Inner) (e:ExtractTest i0 i1) (d0:nat->Type) (d1:nat) :=
    match e with
	     | extractTestI x f t =>
             fun
               _ : match innerI_fun f with
                   | innerI_fun f0 => fun _ : nat -> Type => f0
                   | _ => fun t0 : nat -> Type => t0
                   end d0
                     (match innerI_inner (innerI_nat x) with
                      | innerI_inner i =>
                          match i with
                          | innerI_nat x0 => fun _ : nat => x0
                          | _ => fun t0 : nat => t0
                          end
                      | _ => fun t0 : nat => t0
                      end d1) =>
             t
         | extractTestI_other x f _ =>
             fun
               H : match innerI_fun f with
                   | innerI_fun f0 => fun _ : nat -> Type => f0
                   | _ => fun t : nat -> Type => t
                   end d0
                     (match innerI_inner (innerI_nat x) with
                      | innerI_inner i =>
                          match i with
                          | innerI_nat x0 => fun _ : nat => x0
                          | _ => fun t : nat => t
                          end
                      | _ => fun t : nat => t
                      end d1) =>
             H
         | extractTestI_extra inner =>
             fun
               H : match inner with
                   | innerI_fun f => fun _ : nat -> Type => f
                   | _ => fun t : nat -> Type => t
                   end d0
                     (match inner with
                      | innerI_inner i =>
                          match i with
                          | innerI_nat x => fun _ : nat => x
                          | _ => fun t : nat => t
                          end
                      | _ => fun t : nat => t
                      end d1) =>
             H
         | extractTestI_extra_const =>
             fun
               H : match innerI_extra with
                   | innerI_fun f => fun _ : nat -> Type => f
                   | _ => fun t : nat -> Type => t
                   end d0
                     (match innerI_extra with
                      | innerI_inner i =>
                          match i with
                          | innerI_nat x => fun _ : nat => x
                          | _ => fun t : nat => t
                          end
                      | _ => fun t : nat => t
                      end d1) =>
             H
         end.

Print extract.


Definition extract (i0 i1 :Inner) (e: ExtractTest i0 i1) (d0:nat->Type) (d1:nat) :=
match e in ExtractTest i0 i1 return 
(match i1 with
| innerI_fun f0 => fun _ : nat -> Type => f0
| _ => fun t0 : nat -> Type => t0
end d0
    (match i0 with
    | innerI_inner i =>
        match i with
        | innerI_nat x0 => fun _ : nat => x0
        | _ => fun t0 : nat => t0
        end
    | _ => fun t0 : nat => t0
    end d1))
-> 
(match i1 with
| innerI_fun f0 => fun _ : nat -> Type => f0
| _ => fun t0 : nat -> Type => t0
end d0
    (match i0 with
    | innerI_inner i =>
        match i with
        | innerI_nat x0 => fun _ : nat => x0
        | _ => fun t0 : nat => t0
        end
    | _ => fun t0 : nat => t0
    end d1)) 
with 
| extractTestI x f t => fun _ => t 
| _ => fun t => t 
end.
Print extract.

Lemma congruence_test (x : nat) (f : nat -> Type) t1 t2 : extractTestI x f t1 = extractTestI x f t2 -> t1 = t2.
Proof.
Fail congruence.
intros E.
apply (f_equal (fun e => extract  (innerI_inner (innerI_nat x)) (innerI_fun f) e f x t1)) in E.
cbn in E.
exact E.
Qed.

BuildProjectable extractTestI 2.


BuildProjectable S 0.


IsProjectable S 0.


IsProjectable extractTestI 2.

Definition proj_extract_test_x (inner_ix:Inner) : nat -> nat.
Proof.
refine (match inner_ix with 
    | innerI_inner inner_x => 
        match inner_x with 
        | innerI_nat x => fun _ => x 
        | _ => fun t => t
        end
    | _ => fun t => t
    end).
Defined.

Definition proj_extract_test_f (inner_f:Inner) : (nat -> Type) -> nat -> Type.
Proof.
refine (match inner_f with 
    | innerI_fun f => fun _ => f
    | _ => fun t => t
    end).
Defined.


Definition extract 
  (i1 : Inner)
  (i2 : Inner)
  (e : ExtractTest i1 i2) 
  (x1 : nat -> Type)
  (x2 : nat):
    (proj_extract_test_f i2 x1) (proj_extract_test_x i1 x2) -> 
    (proj_extract_test_f i2 x1) (proj_extract_test_x i1 x2).
Proof.
refine (match e with
| extractTestI _ _ t => fun _ => t
| _ => fun t => t
end).
Defined.

Print extract.

Lemma congruence_test (x : nat) (f : nat -> Type) t1 t2 : extractTestI x f t1 = extractTestI x f t2 -> t1 = t2.
Proof.
Fail congruence.
intros E.
apply (f_equal (fun e => extract f x (innerI_inner (innerI_nat x)) (innerI_fun f) e t1)) in E.
cbn in E.
exact E.
Qed.


Inductive DirectExtraction : Inner -> (nat->Type) -> Type :=
| extractDirectTestI : forall (x:nat) (f:nat->Type) (t:f x),
DirectExtraction (innerI_inner (innerI_nat x)) f
| extractDirectTestI_other : forall (x:nat) (f:nat->Type) (t:f x), DirectExtraction (innerI_inner (innerI_nat x)) f
| extractDirectTestI_extra : forall inner, DirectExtraction inner (fun _ => unit)
| extractDirectTestI_extra_const: DirectExtraction innerI_extra (fun _ => unit).

Definition proj_direct_f (e:nat->Type) : (nat->Type)->(nat->Type) :=
    fun _ => e.

Definition extract_direct 
(x : nat)
(f : nat -> Type)
inner1 
(e : DirectExtraction inner1 f) :
    (proj_direct_f f f) (proj_extract_test_x inner1 x) -> 
    (proj_direct_f f f) (proj_extract_test_x inner1 x).
Proof.
refine (match e with
| extractDirectTestI _ _ t => fun _ => t
| _ => fun t => t
end).
Defined.

Lemma congruence_direct_test (x : nat) (f : nat -> Type) t1 t2 : extractDirectTestI x f t1 = extractDirectTestI x f t2 -> t1 = t2.
Proof.
Fail congruence.
intros E.
apply (f_equal (fun e => extract_direct x f (innerI_inner (innerI_nat x)) e t1)) in E.
cbn in E.
exact E.
Qed.
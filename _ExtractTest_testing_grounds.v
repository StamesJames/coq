MyHelloWorld.

Inductive TestInd (u:unit) : (nat->Type)->nat->Type :=
|  testI : forall f x, f x -> TestInd u f x. 

Inductive Inner : Type :=
| innerI_nat : forall (x:nat), Inner
| innerI_fun : forall (f:nat->Type), Inner
| innerI_inner : forall (i:Inner), Inner
| innerI_extra : Inner.

Inductive ExtractTestParam (A:Type): Inner -> Inner -> unit -> Type :=
| extractTestPI : unit -> unit -> forall (x:nat) (f:nat->Type) (t:f x),
ExtractTestParam A (innerI_inner (innerI_nat x)) (innerI_fun f) tt
| extractTestPI_other : forall (x:nat) (f:nat->Type) (t:f x), ExtractTestParam A (innerI_inner (innerI_nat x)) (innerI_fun f) tt
| extractTestPI_extra : forall inner, ExtractTestParam A inner inner tt
| extractTestPI_extra_const: ExtractTestParam A innerI_extra innerI_extra tt.

Lemma congruenceParam_test (B:Type) (y : nat) (g : nat -> Type) t1 t2 : extractTestPI B tt tt y g t1 = extractTestPI B tt tt y g t2 -> t1 = t2.
Proof.
congruence.
intros H.
apply (
    f_equal
    (fun
	                       e : ExtractTestParam B
                                 (innerI_inner (innerI_nat y)) 
                                 (innerI_fun g) tt =>
                         match
                           e in (ExtractTestParam _ i i0 u)
                           return
                             (fun
                                _ : match i0 with
                                    | innerI_fun f => f
                                    | _ => g
                                    end
                                      match i with
                                      | innerI_inner i1 =>
                                          match i1 with
                                          | innerI_nat x => x
                                          | _ => y
                                          end
                                      | _ => y
                                      end =>
                              match i0 with
                              | innerI_fun f => f
                              | _ => g
                              end
                                match i with
                                | innerI_inner i1 =>
                                    match i1 with
                                    | innerI_nat x => x
                                    | _ => y
                                    end
                                | _ => y
                                end)
                         with
                         | extractTestPI _ _ _ x f t =>
                             fun
                               _ : match innerI_fun f with
                                   | innerI_fun f0 => f0
                                   | _ => g
                                   end
                                     match innerI_inner (innerI_nat x) with
                                     | innerI_inner i =>
                                         match i with
                                         | innerI_nat x0 => x0
                                         | _ => y
                                         end
                                     | _ => y
                                     end =>
                             t
                         | extractTestPI_other _ x f _ =>
                             fun
                               t : match innerI_fun f with
                                   | innerI_fun f0 => f0
                                   | _ => g
                                   end
                                     match innerI_inner (innerI_nat x) with
                                     | innerI_inner i =>
                                         match i with
                                         | innerI_nat x0 => x0
                                         | _ => y
                                         end
                                     | _ => y
                                     end =>
                             t
                         | extractTestPI_extra _ inner =>
                             fun
                               t : match inner with
                                   | innerI_fun f => f
                                   | _ => g
                                   end
                                     match inner with
                                     | innerI_inner i =>
                                         match i with
                                         | innerI_nat x => x
                                         | _ => y
                                         end
                                     | _ => y
                                     end =>
                             t
                         | extractTestPI_extra_const _ =>
                             fun
                               t : match innerI_extra with
                                   | innerI_fun f => f
                                   | _ => g
                                   end
                                     match innerI_extra with
                                     | innerI_inner i =>
                                         match i with
                                         | innerI_nat x => x
                                         | _ => y
                                         end
                                     | _ => y
                                     end =>
                             t
                         end t1)
) in H.

congruence.
Qed.
(*
Lemma extraction_TestInd u f x t1 t2 : testI u f x t1 = testI u f x t2 -> t1 = t2.
Proof.
congruence.
Qed. *)




       
Lemma congruenceParam_test (B:Type) (y : nat) (g : nat -> Type) t1 t2 : extractTestPI B y g t1 = extractTestPI B y g t2 -> t1 = t2.
Proof.
intros H.
apply 
(f_equal
    (fun e : ExtractTestParam B (innerI_inner (innerI_nat y)) (innerI_fun g) =>
   match
     e in (ExtractTestParam _ i i0)
     return
       (match i0 in Inner with
        | innerI_fun f => f
        | _ => g
        end 
          (match i with
           | innerI_inner i1 =>
               match i1 with
               | innerI_nat x => x
               | _ => y
               end
           | _ =>  y
           end)) ->
         (match i0 with
         | innerI_fun f => f
         | _ => g
         end 
         (match i with
             | innerI_inner i1 =>
                 match i1 with
                 | innerI_nat x => x
                 | _ => y
                 end
             | _ =>  y
             end))
   with
   | extractTestPI _ x f t =>
       fun
         _ : match innerI_fun f with
             | innerI_fun f0 => f0
             | _ => g
             end 
               (match innerI_inner (innerI_nat x) with
                | innerI_inner i =>
                    match i with
                    | innerI_nat x0 => x0
                    | _ => y
                    end
                | _ => y
                end) =>
       t
   | extractTestPI_other _ x f _ =>
       fun
         H1 : match innerI_fun f with
              | innerI_fun f0 => f0
              | _ => g
              end
                 (match innerI_inner (innerI_nat x) with
                 | innerI_inner i =>
                     match i with
                     | innerI_nat x0 =>  x0
                     | _ => y
                     end
                 | _ => y
                 end) =>
       H1
   | extractTestPI_extra _ inner =>
       fun
         H1 : match inner with
              | innerI_fun f =>  f
              | _ => g
              end 
                (match inner with
                 | innerI_inner i =>
                     match i with
                     | innerI_nat x =>  x
                     | _ => y
                     end
                 | _ => y
                 end ) =>
       H1
   | extractTestPI_extra_const _ =>
       fun
         H1 : match innerI_extra with
              | innerI_fun f =>  f
              | _ => g
              end 
                (match innerI_extra with
                 | innerI_inner i =>
                     match i with
                     | innerI_nat x => x
                     | _ => y
                     end
                 | _ => y
                 end ) =>
       H1
   end t1)
) in H.



Inductive Inner : Type :=
| innerI_nat : forall (x:nat), Inner
| innerI_fun : forall (f:nat->Type), Inner
| innerI_inner : forall (i:Inner), Inner
| innerI_extra : Inner.

Inductive ExtractTestParam (A:Type): Inner -> Inner -> Type :=
| extractTestPI : forall (x:nat) (f:nat->Type) (t:f x),
ExtractTestParam A (innerI_inner (innerI_nat x)) (innerI_fun f) 
| extractTestPI_other : forall (x:nat) (f:nat->Type) (t:f x), ExtractTestParam A (innerI_inner (innerI_nat x)) (innerI_fun f) 
| extractTestPI_extra : forall inner, ExtractTestParam A inner inner
| extractTestPI_extra_const: ExtractTestParam A innerI_extra innerI_extra.
.
apply
(f_equal (
(fun
   e : ExtractTestParam B (innerI_inner (innerI_nat y))
         (innerI_fun g) =>
 (fun (A : Type) (H H0 : Inner)
    (e0 : ExtractTestParam A H H0) 
    (d0 : nat -> Type) (d1 : nat) =>
  match
    e0 in (ExtractTestParam _ i i0)
    return
      (match i0 with
       | innerI_fun f => fun _ : nat -> Type => f
       | _ => fun t : nat -> Type => t
       end d0
         (match i with
          | innerI_inner i1 =>
              match i1 with
              | innerI_nat x => fun _ : nat => x
              | _ => fun t : nat => t
              end
          | _ => fun t : nat => t
          end d1) ->
       match i0 with
       | innerI_fun f => fun _ : nat -> Type => f
       | _ => fun t : nat -> Type => t
       end d0
         (match i with
          | innerI_inner i1 =>
              match i1 with
              | innerI_nat x => fun _ : nat => x
              | _ => fun t : nat => t
              end
          | _ => fun t : nat => t
          end d1))
  with
  | extractTestPI _ x f t =>
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
  | extractTestPI_other _ x f _ =>
      fun
        H1 : match innerI_fun f with
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
      H1
  | extractTestPI_extra _ inner =>
      fun
        H1 : match inner with
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
      H1
  | extractTestPI_extra_const _ =>
      fun
        H1 : match innerI_extra with
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
      H1
  end) B (innerI_inner (innerI_nat y)) 
   (innerI_fun g) e g y t1)
)H ).
Defined.


Inductive ListIndexed : Type -> Type :=
| NilI : forall A, ListIndexed A 
| ConsI : forall A, A -> ListIndexed A -> ListIndexed A.


Goal forall A (x: A) (l l': ListIndexed A), ConsI A x l = ConsI A x l' -> l = l'.
Proof.
congruence.
Qed.


Inductive List A : Type :=
| Nil : List A 
| Cons : A -> List A -> List A.

Goal forall A (x: A) (l l': List A), Cons A x l = Cons A x l' -> l = l'.
Proof.
congruence.
Qed.

Inductive ListIndexedParam (B:Type) : Type -> Type :=
| NilIP : forall A, ListIndexedParam B A 
| ConsIP : forall A, A -> ListIndexedParam B A -> ListIndexedParam B A.

Goal forall A B (x: A) (l l': ListIndexedParam B A), ConsIP B A x l = ConsIP B A x l' -> l = l'.
Proof.
congruence.
intros A B x l l' H.
apply (f_equal
(fun e : ListIndexedParam B A =>
	        (fun (B H : Type) (e0 : ListIndexedParam B H) (d0 d1 : Type) =>
             match
               e0 in (ListIndexedParam _ T)
               return
                 (ListIndexedParam ((fun _ : Type => d1) d0)
                    ((fun _ : Type => T) d1) ->
                  ListIndexedParam ((fun _ : Type => d1) d0)
                    ((fun _ : Type => T) d1))
             with
             | NilIP _ A =>
                 fun
                   H0 : ListIndexedParam ((fun _ : Type => d1) d0)
                          ((fun _ : Type => A) d1) =>
                 H0
             | ConsIP _ A _ x =>
                 fun
                   _ : ListIndexedParam ((fun _ : Type => d1) d0)
                         ((fun _ : Type => A) d1) =>
                 x
             end) B A e B A l) 
) in H.
congruence.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
congruence.
Qed.



Inductive ExtractTest : Inner -> Inner -> Type :=
| extractTestI : forall (x:nat) (f:nat->Type) (t:f x),
ExtractTest (innerI_inner (innerI_nat x)) (innerI_fun f) 
| extractTestI_other : forall (x:nat) (f:nat->Type) (t:f x), ExtractTest (innerI_inner (innerI_nat x)) (innerI_fun f) 
| extractTestI_extra : forall inner, ExtractTest inner inner
| extractTestI_extra_const: ExtractTest innerI_extra innerI_extra .

Lemma congruence_test (A:Type) (x : nat) (f : nat -> Type) t1 t2 : extractTestI x f t1 = extractTestI  x f t2 -> t1 = t2.
Proof.
congruence.
Defined.






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
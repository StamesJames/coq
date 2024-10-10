(** * Basic First-Order Logic *)
(** ** Syntax *)

Require Vector.

(* Signatures are a record to allow for easier definitions of general transformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (* We use the stdlib definition of vectors to be maximally compatible  *)

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), Vector.t term (ar_syms f) -> term.
  Arguments func _ _ : clear implicits. (* Temporarily make it fully explicit *)

  Set Elimination Schemes.

  Context {Σ_preds : preds_signature}.

  (* We use a flag to switch on and off a constant for falisity *)

  Inductive falsity_flag := falsity_off | falsity_on.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.

  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), Vector.t term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b.
  Arguments form {_}.
  Arguments atom {_} _ _, _ _ _.
  Arguments bin {_} _ _ _, _ _ _ _.

End fix_signature.

(* Fragment syntax *)

Module FragmentSyntax.

  Inductive frag_logic_binop : Type :=
  | Impl : frag_logic_binop.

  Inductive frag_logic_quant : Type :=
  | All : frag_logic_quant.

  Definition frag_operators : operators :=
    {| binop := frag_logic_binop ; quantop := frag_logic_quant |}.

  #[export] Hint Immediate frag_operators : typeclass_instances.

  Declare Scope fragment_syntax.

  #[global] Open Scope fragment_syntax.
  Notation "phi → psi" := (@bin _ _ frag_operators _ Impl phi psi) (at level 43, right associativity) : fragment_syntax.
  Notation "¬ phi" := (phi → falsity) (at level 42) : fragment_syntax.
End FragmentSyntax.

Import FragmentSyntax.

Inductive syms_func := s_f : bool -> syms_func | s_e.

#[global]
Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => if f then 1 else 0 |}.

Inductive syms_pred := sPr | sQ.

#[global]
Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := fun P => if P then 2 else 0 |}.

Lemma test (s t q: form falsity_off) : q → s = q → t -> s = t.
Proof.
  congruence.
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type type_extraction =
(* The term that is getting extracted *)
| Id of EConstr.t
(* The rel term that is getting extracted, the rel term from wich its getting extracted, The constructor from which to extract, Type of the Cosntructor that is getting extracted, index (1 based) to extract from, further extraction *)
| Extraction of (EConstr.t * EConstr.t * (Names.constructor * EConstr.EInstance.t) * EConstr.t * int * type_extraction)

type type_composition =
(* env type to compose *)
| FromEnv of EConstr.t
(* env type to compose, env parameter term to extract from, index (1 based) of parameter, extraction for the given type*)
| FromParameter of EConstr.t * EConstr.t * int * type_extraction
(* env type to compose, rel index term to extract from, index (1 based) index to compose from, extraction for the given type *)
| FromIndex of EConstr.t * EConstr.t * int * type_extraction
(* (env f type to compose, composition for f), array of (env arg type to compose, composition for arg)*)
| Composition of (EConstr.t * type_composition) * (EConstr.t * type_composition) array

type projection_type =
| Simple
| Dependent of type_composition
| NotProjectable

val projectability_test : 
  Environ.env ->
  Evd.evar_map ->
  Names.constructor * EConstr.EInstance.t ->
  int ->
  Evd.econstr ->
  Names.inductive EConstr.puniverses ->
  Evd.econstr array ->
  Evd.econstr array ->
  Evd.evar_map * projection_type

val build_projection :
  Environ.env ->
  Evd.evar_map ->
  Constr.pconstructor ->
  int ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.types ->
  Evd.evar_map * EConstr.t

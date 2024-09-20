Require Import Koika.Frontend.
(* Require Import Coq.Init.Hexadecimal. *)
Require Import Coq.Init.Nat.
Require Import Coq.Init.Decimal.
Require Import Coq.Init.Number.
(* Require Import Coq.Numbers.BinNums. *)
(* Require Import Coq.NArith.BinNatDef. *)

Notation "'|' x 'b~' y '|'" :=
  (Bits.of_N x (N.of_num_uint y%uint)) (in custom koika, x constr at level 0 , y constr at level 0).

Inductive empty_reg_t := .
Definition empty_R (reg : empty_reg_t) : type :=
    empty_reg_t_rect (fun _ : empty_reg_t => type) reg.
Definition empty_r (reg : empty_reg_t) : type_denote (empty_R reg) :=
    empty_reg_t_rect (fun _ : empty_reg_t => type_denote (empty_R reg)) reg.

(* Registernamen *)
Inductive reg_t :=
  | SOME_REG
  | ANOTHER_REG
  .

(* Registertypen *)
Definition R (reg: reg_t) : type :=
  match reg with
  | SOME_REG    => bits_t 32
  | ANOTHER_REG => bits_t 16
  end.


(* Startbelegung der Register *)
Definition r (reg : reg_t) : R reg :=
  match reg with
  | SOME_REG    => {{ |32b~ 0x00000401| }}
  | ANOTHER_REG => {{ |16b~ 0x1234| }}
  end.

Definition some_func : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun some_func (value: bits_t 32) : bits_t 32 =>
  value + read0(SOME_REG)
}}.
Definition some_func_tc := (tc_function R empty_Sigma some_func).

Definition addition {reg_t} : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun addition (value: bits_t 32) : bits_t 32 =>
  value + |32`d57|
}}.
Definition addition_tc := (tc_function empty_R empty_Sigma (@addition empty_reg_t)).

Definition writing : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun writing (value: bits_t 32) : unit_t =>
  write0(SOME_REG, value)
}}.
Definition writing_tc := (tc_function R empty_Sigma writing).

(* Definition subtraction {reg_t : Type} : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun subtraction (value: bits_t 32) : bits_t 32 =>
  value - |32`d89|
}}.
Definition subtraction_tc := (tc_function empty_R empty_Sigma (@subtraction empty_reg_t)). *)

Definition reading : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun reading () : bits_t 32 =>
  read0(SOME_REG)
}}.
Definition reading_tc := (tc_function R empty_Sigma reading).

Definition combining : UInternalFunction reg_t empty_ext_fn_t :=
{{
fun combining () : unit_t =>
  write0(SOME_REG, addition(reading()))
}}.

Definition combining_tc := (tc_function R empty_Sigma combining).
 
(* Theorem combining_splitted :
  forall (env : ContextEnv.(env_t) koika.R) Gamma Gamma' sched_log action_log action_log' out,
  interp_action env empty_sigma Gamma sched_log action_log combining_tc
    = Some(action_log', out, Gamma').
Proof.
  intros.
  unfold combining_tc, combining.
  unfold int_argspec, int_retSig, int_body.
  Unset Printing Notations.
  cbv delta [interp_action] beta. cbv fix. simpl.

  simpl (extract_success _).
  Opaque USugar.
  cbv beta.


  lazy delta [desugar_action desugar_action'].
  lazy fix match beta iota zeta.
  eval compute in (desugar_action _ _).
  unfold desugar_action, desugar_action'.
  simpl.
  cbv fix.
  simpl (desugar_action' _ _ _ _).
  unfold TypeInference.tc_action.

  unfold int_body.
  unfold desugar_action. *)

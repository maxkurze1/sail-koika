Require sail.sail.
Require sail.sail_types.
Require koika.koika.
Require Import Prelude.
Require Import Koika.Frontend.
Require Import Koika.Testing.
Require Import Sail.Base.
(* Require Import Sail.Values. *)
Require Import Sail.State_lifting.
Require Import Sail.State_monad.
Require Import Nat.
Require Import proof.proof_common.

Require Import List.
Import List.ListNotations.

Definition koika_env_idk  :=
  (fun n1 n2 =>
  #{
      koika.SOME_REG    => Bits.of_nat 32 n2;
      koika.ANOTHER_REG => Bits.of_nat 16 n1
  }#
  ) : forall (n1 n2 : nat),  ContextEnv.(env_t) (fun (x : koika.reg_t) => koika.R x).

Definition koika_unit := Bits.nil.

Theorem combining_equality :
  forall n1 n2 : nat,

  let sail_in := tt in
  let koika_in := CtxEmpty in

  let sail_r :=
  {|
    sail_types.ANOTHER_REG := Word.natToWord 16 n1;
    sail_types.SOME_REG    := Word.natToWord 32 n2
  |} in

  let koika_r :=
    ContextEnv.(create) (fun (reg : koika.reg_t) =>
    match reg with
    | koika.ANOTHER_REG => Bits.of_nat 16 n1
    | koika.SOME_REG    => Bits.of_nat 32 n2
    end : (koika.R reg)) in

  (* koika *)
  assert Some (koika_r', koika_out) := koika_eval koika_r koika.combining_tc koika_in in

  (* sail *)
  assert [(Value sail_out,{|ss_regstate := sail_r'|},_)] := sail_eval sail_r sail.combining sail_in in

  (* actual condition *)
  koika_out = koika_unit /\
  sail_out = tt /\
  sail_koika_reg_eq sail_r' koika_r'.
Proof.
  intros n1 n2 sail_r koika_r.
  cbn in koika_r.
  unfold sail_eval, koika_eval.
  simpl (interp_action _ _ _ _ _ _).
  cbv match.
  cbn. simpl.
  repeat split.
  unfold sail_koika_reg_eq.
  destruct reg; [apply bits_word_add; try reflexivity| ..];
  apply bits_word_to_nat_of_nat; reflexivity.
Defined.

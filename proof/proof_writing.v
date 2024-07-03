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

Theorem sail_reading_some_reg_always_00005678 :
  assert [(Value _,{| ss_regstate := {| sail_types.SOME_REG := some |} |}, _)] :=
    sail_eval sail.initial_regstate sail.writing (Ox"00005678") in
  some = (Ox"00005678").
Proof.
  reflexivity.
Defined.


Definition koika_env_idk  :=
  (fun n1 n2 =>
  #{
      koika.SOME_REG    => Bits.of_nat 32 n2;
      koika.ANOTHER_REG => Bits.of_nat 16 n1
  }# ) : forall (n1 n2 : nat),  ContextEnv.(env_t) (fun (x : koika.reg_t) => koika.R x).


Theorem writing_equality :
  forall n n1 n2 : nat,

  let koika_in :input := #{ ("value", bits_t 32) => (Bits.of_nat 32 n) }# in
  let sail_in  := (Word.natToWord 32 n) in

  let sail_r :=
  {|
      sail_types.ANOTHER_REG := Word.natToWord 16 n1;
      sail_types.SOME_REG    := Word.natToWord 32 n2
  |} in

  (* let koika_r :=
      ContextEnv.(create) (fun (reg : koika.reg_t) =>
      match reg with
      | koika.ANOTHER_REG => Bits.of_nat 16 n1
      | koika.SOME_REG    => Bits.of_nat 32 n2
      end : (koika.R reg)) in *)

  let koika_r := koika_env_idk n1 n2 in
  (* koika *)
  assert Some (koika_r', koika_out) := koika_eval koika_r koika.writing_tc koika_in in

  (* sail *)
  assert [(Value _, {| ss_regstate := sail_r' |} , _)] := sail_eval sail_r sail.writing sail_in in

  (* actual condition *)
  sail_koika_reg_eq sail_r' koika_r'.
Proof.
  intros n n1 n2 koika_in sail_in sail_reg koika_r.
  cbn in koika_r.
  unfold koika_eval.
  simpl (interp_action _ _ _ _ _ _).
  cbv match.
  cbn.
  unfold sail_in, sail_koika_reg_eq.
  destruct reg; apply bits_word_to_nat_of_nat; reflexivity.
Defined.


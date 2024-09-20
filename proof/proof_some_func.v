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

Definition input { sig : list (string * type) } := context ( fun (x : (string * type)) => (snd x) ) sig.

Check (#{ ("value", bits_t 32) => (Bits.of_nat 32 89) }# : input).

Check (fun n_ar n_sr => (#{
  koika.SOME_REG    => Bits.of_nat 32 n_sr;
  koika.ANOTHER_REG => Bits.of_nat 16 n_ar
}# : context koika.R _ ) : ContextEnv.(env_t) koika.R ).

Theorem idk:
  forall (n_in : nat) (koika_r : ContextEnv.(env_t) koika.R),

  let koika_in : input := #{ ("value", bits_t 32) => (Bits.of_nat 32 n_in) }# in

  (* let koika_r :=
  (#{
    koika.SOME_REG    => Bits.of_nat 32 50;
    koika.ANOTHER_REG => Bits.of_nat 16 50
  }# : context koika.R _ ) : ContextEnv.(env_t) koika.R in *)

  True.
Proof. intros. exact I. Defined.

Notation "s 's=k' k" := (sail_koika_reg_eq s k) (no associativity,at level 69).

Theorem some_func_equality:
  forall (n : nat)
    (koika_r : ContextEnv.(env_t) koika.R)
    (sail_r : sail_types.regstate),

  let koika_in := #{ ("value", bits_t 32) => (Bits.of_nat 32 n) }# in
  let sail_in  := Word.natToWord 32 n in

  sail_r s=k koika_r ->

  (* koika *)
  assert Some (koika_r', koika_out) :=
    koika_eval koika_r koika.some_func_tc koika_in in
  (* sail *)
  assert [(Value sail_out,{|ss_regstate := sail_r'|},_)] :=
    sail_eval sail_r sail.some_func sail_in in

  (* actual condition *)
  Bits.to_nat koika_out = Word.wordToNat sail_out  /\
  sail_r' s=k koika_r'.
Proof.
  intros.
  unfold koika_eval, sail_eval.

  (* cbn in koika_r. *)
  simpl (interp_action _ _ _ _ _ _).
  cbv match.
  cbn.
  split.
  - apply bits_word_add.
    + unfold sail_in.
      apply bits_word_to_nat_of_nat.
      reflexivity.
    + unfold sail_koika_reg_eq in H.
      exact (H koika.SOME_REG).
  - unfold sail_koika_reg_eq.
    intro reg.
    exact (H reg).
Defined.
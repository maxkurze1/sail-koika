Require sail.sail.
Require koika.koika.
Require Prelude.

Require Import Nat.

Require Import Koika.Frontend.
Require Import Koika.Testing.
Require Import Sail.MachineWord.
Require Import proof.proof_common.
Import Values.

Theorem sail_addition_to_0 : sail.addition(Ox"00000000") = (Ox"00000039").
Proof.
    (* unfold sail.addition. *)
    (* vm_compute. *)
    reflexivity.
Defined.

Theorem addition_equality_0:
  let koika_in := #{ ("value", bits_t 32) => (Bits.of_nat 32 0) }# in 

  assert Some (_, out) := koika_eval (ContextEnv.(create) koika.empty_r) koika.addition_tc koika_in in
  Bits.to_nat out =  Word.wordToNat (sail.addition (Ox"00000000")).
Proof.
  reflexivity.
Defined.

Lemma log_find_empty :
  forall reg_t env R reg, @latest_write reg_t R env log_empty reg = None.
Proof.
  intros.
  unfold latest_write, log_find, log_empty.
  rewrite getenv_create.
  reflexivity.
Defined.

Theorem addition_equality_general:
  forall n r,

  let koika_in := #{ ("value", bits_t 32) => (Bits.of_nat 32 n) }# in
  let sail_in  := Word.natToWord 32 n in

  assert Some (r', koika_out) := (koika_eval r koika.addition_tc koika_in) in
  let sail_out := sail.addition sail_in in

  forall reg, r.[reg] = r'.[reg] /\
  Bits.to_nat koika_out = Word.wordToNat sail_out.
Proof.
  intros.
  unfold koika_eval in *.
  simpl interp_action.
  cbv match.
  split.
  - destruct reg.
  - unfold sail_in.
    unfold sail.addition. simpl.
    apply bits_word_add.
    + apply bits_word_to_nat_of_nat2.
    + reflexivity.
Defined.

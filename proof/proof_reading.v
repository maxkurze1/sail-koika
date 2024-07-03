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

Theorem sail_reading_init_401 :
  assert [(Value v, _ , _)] := sail_eval sail.initial_regstate sail.reading tt in
  v = (Ox"00000401").
Proof.
  reflexivity.
Defined.

Theorem koika_reading_init_1025 :
  assert Some(r', v) := koika_eval (ContextEnv.(create) koika.r) koika.reading_tc CtxEmpty in
  Bits.to_nat v = 1025%nat.
Proof.
  reflexivity.
Defined.

Theorem reading_initial_equality :
  assert Some (_, koika_out) := koika_eval (ContextEnv.(create) koika.r) koika.reading_tc CtxEmpty in
  assert [(Value sail_out, _ , _)] := sail_eval sail.initial_regstate sail.reading tt in

  Word.wordToNat sail_out = Bits.to_nat koika_out.
Proof.
   reflexivity.
Defined.

Theorem reading_equality :
  forall (n1 : nat) (n2 : nat),

  let sail_r :=
  {|
      sail_types.ANOTHER_REG := Word.natToWord 16 n1;
      sail_types.SOME_REG    := Word.natToWord 32 n2
  |} in

  let koika_env :=
    ContextEnv.(create) (fun (reg : koika.reg_t) =>
    match reg with
    | koika.ANOTHER_REG => Bits.of_nat 16 n1
    | koika.SOME_REG    => Bits.of_nat 32 n2
    end : (koika.R reg)) in

  (* koika *)
  assert Some (koika_r', koika_out) := koika_eval koika_env koika.reading_tc CtxEmpty in

  (* sail *)
  assert [(Value sail_out, {| ss_regstate := sail_r' |} , _)] := sail_eval sail_r sail.reading tt in
  
  (* actual condition *)
  sail_koika_reg_eq sail_r' koika_r' /\
  sail_out =nat (koika_out : bits 32).
Proof.
  intros n1 n2 sail_reg koika_env.
  unfold koika_eval, sail_eval.
  simpl (interp_action _ _ _ _ _ _).
  cbv match.
  split.
  - unfold sail_koika_reg_eq.
    destruct reg; apply bits_word_to_nat_of_nat; reflexivity.
  - apply eq_sym, bits_word_to_nat_of_nat, eq_refl.
Defined.
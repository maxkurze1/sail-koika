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

Require koika.riscv.
Require sail.riscv.
Require sail.riscv_types.

Locate alu32.

Definition koika_eval
  { reg_t : Type }
 `{ FiniteType reg_t }
  { sig : tsig var_t }
  { tau }
  { R : reg_t -> type }
  ( env: env_t ContextEnv R )
  ( func : action R empty_Sigma sig tau )
  ( inputs : input )
  (* : option ((ContextEnv) * tau) *) :=
    match (interp_action env empty_sigma inputs log_empty log_empty func) with
    | Some (log,out,_) =>
      let ctxt := commit_update env log in
      Some (ctxt,out)
    | None => None
    end.

(* Definition convert_tuple {A B} : (A * B) ->  *)

Notation "(( a , .. , b ))" :=
  (CtxCons (_,_) a .. (CtxCons (_,_) b CtxEmpty) ..)
  (at level 0, 
  a constr at level 80,
  b constr at level 80).

Definition sail_eval {A B C D E} (func : A -> B -> C -> D -> E) (inp : A * B * C * D) :=
  let '(a,b,c,d) := inp in
  func a b c d.

Notation "a '=nat' b" := (@eq nat (a : bits _) (b : mword _) ) (at level 69).

Theorem addition_refinement_general:
  forall a b r,

  (* let koika_in :=  #{
    ("funct3", bits_t 3) => koika.riscv.funct3_ADD;
    ("funct7", bits_t 7) => koika.riscv.funct7_ADD;
    ("b", bits_t 32) => (Bits.of_nat 32 b);
    ("a", bits_t 32) => (Bits.of_nat 32 a)
  }# in *)

  let koika_in := ((
    koika.riscv.funct3_ADD,
    koika.riscv.funct7_ADD,
    Bits.of_nat 32 a,
    Bits.of_nat 32 b
  )) : context _ (int_argspec koika.riscv.alu32') in

  let sail_in := (
    sail.riscv_types.funct3_ADD,
    sail.riscv_types.funct7_ADD,
    Word.natToWord 32 a,
    Word.natToWord 32 b
  ) in

  assert Some (r', koika_out) := (koika_eval r koika.riscv.alu32 koika_in) in
  let sail_out := sail_eval sail.riscv.alu32 sail_in in

  (forall reg, r.[reg] = r'.[reg]) /\
  koika_out =nat sail_out.
Proof.
  intros.
  unfold sail_in, sail_eval.
  simpl (sail.riscv.alu32 _ _ _ _).
  unfold koika_eval.
  unfold koika.riscv.alu32.
  vm_compute (extract_success _ _).
  unfold interp_action.
  simpl.
  split.
  - intro reg.
    destruct reg.
  - apply bits_word_add.
    + apply bits_word_to_nat_of_nat2.
    + apply bits_word_to_nat_of_nat2.
Defined.
Require sail.sail.
Require koika.koika.

Require Prelude.
Require Import Nat.
Require Import Koika.Frontend.
Require Import Koika.Testing.
Require Import Sail.MachineWord.
Import Values.

Declare Custom Entry word_consts.
Notation "bs '~' '0'" := (Word.WS false bs) (in custom word_consts at level 1, left associativity, format "bs ~ 0").
Notation "bs '~' '1'" := (Word.WS true bs)  (in custom word_consts at level 1, left associativity, format "bs ~ 1").

Notation "'0'"    := (Word.WS false Word.WO) (in custom word_consts at level 0).
Notation "'1'"    := (Word.WS true Word.WO)  (in custom word_consts at level 0).

Notation "'[w'  number ']'" := (number) (at level 1, number custom word_consts at level 200).

Infix "+mw" := MachineWord.add (at level 50, left associativity).
Infix "-mw" := MachineWord.sub (at level 50, left associativity).
Infix "+w" := Word.wplus (at level 50, no associativity).
Infix "-w" := Word.wminus (at level 50, no associativity).

Inductive bits_word_eq : forall n: nat, Bits.bits n -> Word.word n -> Prop :=
    | bits_word_eq_nil : bits_word_eq 0 (Bits.nil) (Word.WO)
    | bits_word_eq_cons {n bi wo} : forall b: bool, bits_word_eq n bi wo -> bits_word_eq (S n) (Bits.cons b bi) (Word.WS b wo).
Arguments bits_word_eq [n] _ _.

Notation "bits 'b=w' word" := (bits_word_eq bits word) (at level 69, no associativity).

#[warnings="-uniform-inheritance"]
Coercion Bits.to_nat : Bits.bits >-> nat.
Coercion Word.wordToNat : Word.word >-> nat.

Notation "a '=nat' b" := (@eq nat a b) (at level 69).

Notation "'assert' a ':=' b 'in' body" := (match b with | a => body | _ => False end) (at level 200, a pattern).

Definition sail_koika_reg_eq (sail_reg : sail_types.regstate) (koika_reg : env_t ContextEnv koika.R) : Prop :=
  forall reg: koika.reg_t, 
  match reg with
  | koika.SOME_REG    => (koika_reg.[koika.SOME_REG]    : bits _) =nat sail_reg.(sail_types.SOME_REG)
  | koika.ANOTHER_REG => (koika_reg.[koika.ANOTHER_REG] : bits _) =nat sail_reg.(sail_types.ANOTHER_REG)
  end.

(* Theorem bits_word_eq_to_nat :
    forall n b w,
    @bits_word_eq n b w <-> Bits.to_nat b = Word.wordToNat w.
Proof.
  intros n bi wo.
  split.
  - intros H.
    induction H.
    + reflexivity.
    + unfold Bits.to_nat.
      rewrite Bits.to_N_cons.
      simpl (Word.wordToNat _).
      destruct b.
      all: rewrite N2Nat.inj_add, N2Nat.inj_mul.
      1: rewrite Nat.add_1_l.
      2: rewrite Nat.add_0_l.
      apply eq_S.
      all: fold (Bits.to_nat bi).
      all:  rewrite Nat.mul_comm.
      all: apply Nat.mul_cancel_r; [lia | ..].
      all: assumption.
  - intros H.
    induction wo.
    + destruct bi.
      exact bits_word_eq_nil.
    + destruct bi.
      enough (E: b = vhd).
      rewrite E.
      apply bits_word_eq_cons.
      apply (IHwo vtl).
      simpl (Word.wordToNat _) in H. *)


Class isomorph (A B : Type) := {
    a_to_b : A -> B;
    b_to_a : B -> A;
    l1: forall b, a_to_b (b_to_a b) = b;
    l2: forall a, b_to_a (a_to_b a) = a
}.

Definition bits_to_word {n : nat} : Bits.bits n -> Word.word n :=
    fun bi =>
    nat_rect (fun n0 : nat => bits n0 -> Word.word n0)
      (fun _ : bits 0 => Word.WO)
      (fun (n0 : nat) (IHn : bits n0 -> Word.word n0) (bi0 : bits (S n0)) =>
       Word.WS (vhd bi0) (IHn (vtl bi0))) n bi.

Fixpoint word_to_bits {n : nat} (w : Word.word n) : Bits.bits n :=
    match w with
    | Word.WO => Bits.nil
    | Word.WS v w' => Bits.cons v (word_to_bits w')
    end.

Instance isomorph_bits_word {n : nat} : isomorph (Bits.bits n) (Word.word n).
Proof.
  unshelve econstructor.
  - exact bits_to_word.
  - exact word_to_bits.
  - intro b.
    induction b.
    + reflexivity.
    + simpl.
      rewrite IHb.
      reflexivity.
  - intro a.
    induction n.
    + induction a.
      reflexivity.
    + induction a.
      simpl. rewrite (IHn vtl).
      reflexivity.
Defined.

Definition koika_to_sail : (forall (reg : koika.reg_t), koika.R reg) -> sail_types.regstate :=
    fun koika_r => {|
        sail_types.ANOTHER_REG := @a_to_b _ _ (@isomorph_bits_word 16) (koika_r koika.ANOTHER_REG) : mword 16;
        sail_types.SOME_REG    := @a_to_b _ _ (@isomorph_bits_word 32) (koika_r koika.SOME_REG)    : mword 32
    |} : sail_types.regstate.

Definition sail_to_koika : sail_types.regstate -> (forall (reg : koika.reg_t), koika.R reg) :=
  fun sail_r => 
    fun (reg : koika.reg_t) =>
      match reg with
      | koika.ANOTHER_REG => @b_to_a _ _ (@isomorph_bits_word 16) (sail_r.(sail_types.ANOTHER_REG)) : bits 16
      | koika.SOME_REG    => @b_to_a _ _ (@isomorph_bits_word 32) (sail_r.(sail_types.SOME_REG))    : bits 32
      end.

Require Import Coq.Logic.FunctionalExtensionality.

Instance register_isomorph_proof : isomorph (forall (reg : koika.reg_t), koika.R reg) sail_types.regstate.
Proof.
    unshelve econstructor.
    - exact koika_to_sail.
    - exact sail_to_koika.
    - intro b.
      unfold sail_to_koika, koika_to_sail.
      rewrite ?(@l1 _ _ (@isomorph_bits_word _) _).
      induction b.
      reflexivity.
    - intro a.
      unfold koika_to_sail, sail_to_koika.
      unfold sail_types.ANOTHER_REG, sail_types.SOME_REG.
      rewrite ?(@l2 _ _ (@isomorph_bits_word _) _).
      extensionality x.
      destruct x; reflexivity.
Defined.

(* Lemma bits_of_nat_surjective :
  forall sz (b : bits sz),
  exists n,
  Bits.of_nat sz n = b.
Proof.
  intros.
  induction sz.
  - destruct b.
    exists 0%nat.
    reflexivity.
  -
  (* Locate "::". *)
  (* Search ( Bits.of_N (vect_cons _ _) = _). *)
  unfold Bits.of_nat.
  (* cbn in b. *)
  (* Print "~". *)
  destruct b.
  fold (@vect_cons bool sz vhd vtl).
  eexists.
  apply Bits.to_N_inj.
  rewrite Bits.to_N_cons.
  (* Search ( Bits.to_N (vect_cons _ _) = _). *)
  (* Search (Bits.to_N (Bits.of_N _ _)). *)
  rewrite Bits.to_N_of_N_mod.
  (* destruct vhd. *)
  (* +  *)
  (* Search ( N.modulo _ _ = _). *)
    rewrite N.mod_small.
    * instantiate (1 := ((if vhd then 1 else 0) + 2 * Bits.to_nat vtl)%nat ).
      destruct vhd.
      all: unfold Bits.to_nat.
      all: rewrite Nat2N.inj_add, Nat2N.inj_mul, N2Nat.id.
      all: reflexivity.
    * destruct vhd.
      assert (2%N = N.of_nat 2%nat); [lia | ..].
      rewrite H.
      rewrite <- Nat2N.inj_pow.
      Search (N.lt N.of_nat _ _).
      rewrite <- Nat2N.inj_lt.

      Search (Bits.to_N _ < _)%nat.
      simpl.
        Search (N.of_nat (N.to_nat _)).
      reflexivity.
      Unset Printing Notations.

      Search (N.of_nat (_ + _)).
    (* 2: {} *)
    2: exact (1 + 2 * Bits.to_nat vtl)%nat.
    reflexivity.
  
  reflexivity.

    simpl.
    exists _. *)


Lemma bits_word_to_nat_of_nat : forall (n1 n2 : nat) (sz : nat),
  n1 = n2 ->
  Bits.to_nat (Bits.of_nat sz n1) = Word.wordToNat (Word.natToWord sz n2).
Proof.
  intros.
  unfold Bits.of_nat, Bits.to_nat.
  rewrite Bits.to_N_of_N_mod, Word.wordToNat_natToWord_eqn.
  rewrite N2Nat.inj_mod, N2Nat.inj_pow, ?Nat2N.id.
  auto with arith.
Defined.

Lemma bits_word_to_nat_of_nat2 : forall (n : nat) (sz : nat),
    Bits.to_nat (Bits.of_nat sz n) = Word.wordToNat (Word.natToWord sz n).
Proof.
    intros. apply bits_word_to_nat_of_nat. reflexivity.
Defined.

Lemma Bits_to_N_to_nat :
    forall sz (b : bits sz),
    N.to_nat (Bits.to_N b) = Bits.to_nat b.
Proof.
    intros. unfold Bits.to_nat. reflexivity.
Defined.

Lemma bits_word_add :
    forall sz (b1 b2 : Bits.bits sz) (w1 w2 : Word.word sz),

    b1 =nat w1 ->
    b2 =nat w2 ->
    b1 +b b2 =nat w1 +w w2.
Proof.
    intros sz b1 b2 w1 w2 H1 H2.
    unfold Bits.to_nat.
    rewrite Bits.to_N_plus, Word.wordToNat_wplus.
    rewrite N2Nat.inj_mod, N2Nat.inj_pow, N2Nat.inj_add, Nat2N.id.
    rewrite ?Bits_to_N_to_nat.
    rewrite H1, H2.
    reflexivity.
Defined.

Lemma bits_word_add2 :  forall (n1 n2 : nat) (sz : nat),
    Bits.to_nat ((Bits.of_nat sz n1) +b (Bits.of_nat sz n2)) = Word.wordToNat ((Word.natToWord sz n1) +mw (Word.natToWord sz n2)).
Proof.
    intros. apply bits_word_add; apply bits_word_to_nat_of_nat2.
Defined.

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

Require Import Sail.State_lifting.
Require Import Sail.State_monad.
Definition sail_eval
  {in_t out_t: Type}
  (r : sail_types.regstate)
  (func: in_t -> sail_types.M out_t)
  (input : in_t)
    := liftState sail_types.register_accessors (func input) (init_state r) default_choice.
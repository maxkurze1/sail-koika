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

Ltac simpl_koika_sail :=
  unfold koika_eval, sail_eval.
  (* repeat match goal with
  | _ => progress 
  | _ => progress unfold sail_eval
  end. *)

Print koika.combining_tc.
Print koika.combining.


(* Lemma interp_single : 
  forall r input R,
  interp_action r empty_sigma input log_empty log_empty
    (tc_function R empty_Sigma 
      
    )
       (extract_success
          (TypeInference.tc_action koika.R empty_Sigma dummy_pos nil
            (bits_t 0)
            (desugar_action dummy_pos
               (UWrite P0 koika.SOME_REG
                  (USugar
                     (UCallModule id Lift_self koika.addition
                        (cons
                           (USugar
                              (UCallModule id Lift_self koika.reading nil))
                           nil)))))) eq_refl) *)


Locate interp_action.

Theorem combining_equality:
  forall n1 n2 : nat,

  let sail_in := tt in
  let koika_in := CtxEmpty in

  let sail_r :=
  {|
    sail_types.ANOTHER_REG := Word.natToWord 16 n1;
    sail_types.SOME_REG    := Word.natToWord 32 n2
  |} in

  let koika_r :=
  (#{
    koika.SOME_REG    => Bits.of_nat 32 n2;
    koika.ANOTHER_REG => Bits.of_nat 16 n1
  }# : context koika.R _ ) : ContextEnv.(env_t) koika.R in

  (* koika *)
  assert Some (koika_r', koika_out) := koika_eval koika_r koika.combining_tc koika_in in

  (* sail *)
  assert [(Value sail_out,{|ss_regstate := sail_r'|},_)] := sail_eval sail_r sail.combining sail_in in

  (* actual condition *)
  koika_out = koika_unit /\
  sail_out = tt /\
  sail_koika_reg_eq sail_r' koika_r'.
Proof.
  intros n1 n2 sail_in koika_in sail_r koika_r.

  simpl_koika_sail.
  rewrite interp_action_cps_correct_rev.

  unfold koika.combining_tc, koika.combining.
  unfold int_argspec, int_retSig, int_body.
  unfold koika.reading.

  Unset Printing Notations.


  (* cbn in koika_r. *)
  simpl (interp_action _ _ _ _ _ _).
  cbv match.
  cbn. simpl.
  repeat split.
  unfold sail_koika_reg_eq.
  destruct reg; [apply bits_word_add; try reflexivity| ..];
  apply bits_word_to_nat_of_nat; reflexivity.
Defined.

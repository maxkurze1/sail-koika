Require Import Koika.Frontend.

Inductive reg_t :=.

Definition funct3_ADD  := Ob~0~0~0.
Definition funct7_ADD  := Ob~0~0~0~0~0~0~0.

Definition funct3_SUB  := Ob~0~0~0.
Definition funct7_SUB  := Ob~0~1~0~0~0~0~0.

Definition funct3_SLL  := Ob~0~0~1.
Definition funct7_SLL  := Ob~0~0~0~0~0~0~0.

Definition funct3_SLT  := Ob~0~1~0.
Definition funct7_SLT  := Ob~0~0~0~0~0~0~0.

Definition funct3_SLTU := Ob~0~1~1.
Definition funct7_SLTU := Ob~0~0~0~0~0~0~0.

Definition funct3_XOR  := Ob~1~0~0.
Definition funct7_XOR  := Ob~0~0~0~0~0~0~0.

Definition funct3_SRL  := Ob~1~0~1.
Definition funct7_SRL  := Ob~0~0~0~0~0~0~0.

Definition funct3_SRA  := Ob~1~0~1.
Definition funct7_SRA  := Ob~0~1~0~0~0~0~0.

Definition funct3_OR   := Ob~1~1~0.
Definition funct7_OR   := Ob~0~0~0~0~0~0~0.

Definition funct3_AND  := Ob~1~1~1.
Definition funct7_AND  := Ob~0~0~0~0~0~0~0.


Definition R (r : reg_t) : type :=
  match r with
  end.

Definition alu32' : UInternalFunction reg_t empty_ext_fn_t := {{
fun alu32 (funct3 : bits_t 3) (funct7 : bits_t 7)
  (a : bits_t 32) (b : bits_t 32) : bits_t 32 =>
    let shamt := b[Ob~0~0~0~0~0 :+ 5] in
    let inst_30 := funct7[|3`d5|] in
    match funct3 with
    | #funct3_ADD  => if (inst_30 == Ob~1) then
                      a - b
                    else
                      a + b
    | #funct3_SLL  => a << shamt
    | #funct3_SLT  => zeroExtend(a <s b, 32)
    | #funct3_SLTU => zeroExtend(a < b, 32)
    | #funct3_XOR  => a ^ b
    | #funct3_SRL  => if (inst_30 == Ob~1) then a >>> shamt else a >> shamt
    | #funct3_OR   => a || b
    | #funct3_AND  => a && b
    return default: #(Bits.of_nat 32 0)
    end
}}.

Definition alu32 := tc_function R empty_Sigma alu32'.
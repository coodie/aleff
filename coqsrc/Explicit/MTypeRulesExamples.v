Require Import Utf8.
Require Import Common.MBinder.
Require Import Explicit.MSyntax.
Require Import Explicit.MTypeRules.
Require Import Coq.Strings.Ascii.

Example Empty_world : world :=
{|
  w_effect_t := Empty_set;
  w_eff_op_t := Empty_function;
  w_eff_ar   := Empty_function;
  w_base_t := Empty_set ;
  w_base_v := Empty_function
|}.

Example ew_var {TV:Set} (n:TV) : typ Empty_world TV := t_var n.

Example row_equivalence_example : 
  〈ew_var 1; ew_var 2; ew_var 3; ew_var 4; ew_var 5〉 ≅ 
  〈ew_var 2; ew_var 1; ew_var 3; ew_var 5; ew_var 4〉.
Proof.
  repeat(
    eapply req_select;
    repeat(
      try (apply row_select_head);
      apply row_select_tail)).
  eapply req_refl.
Qed.

Example row_append_example : row_append
  〈ew_var 1; ew_var 2〉 〈ew_var 3; ew_var 4〉
  〈ew_var 1; ew_var 2;  ew_var 3; ew_var 4〉.
Proof.
  repeat(apply row_append_step).
  apply row_append_base.
Qed.

Inductive Example_effect : Set :=
| IO_effect : Example_effect.

Example IO_effect_operation : Set := inc (inc Empty_set).

Example getc : IO_effect_operation := VZ. 
Example putc : IO_effect_operation := VS VZ.

Inductive Example_base_type : Set :=
| bt_unit : Example_base_type
| bt_char : Example_base_type.

Example Example_world : world :=
{|
  w_effect_t := Example_effect;
  w_eff_op_t := λ e, IO_effect_operation;
  w_eff_ar   := λ _, 0;
  w_base_t   := Example_base_type;
  w_base_v   := λ b, match b with | bt_unit => True | bt_char => ascii end
|}.

Example Example_program := expr Example_world Empty_set Empty_set.
Example Example_typ := typ Example_world Empty_set.

Example print_H : Example_program.
Proof.
  apply e_app.
  { apply e_value.
    apply v_eff_op with IO_effect.
    apply putc. }
  { apply e_value.
    apply v_const with bt_char.
    apply "H"%char. }
Defined.

Example IO_0_stream_Handler (e : Example_program) : Example_program.
Proof.
  apply e_handle with IO_effect.
  { apply nil. }
  { apply e. }
  { apply h_op.
    { apply e_app.
      { apply e_value.
        apply v_var.
        apply V2_resume. }
      apply e_value.
      apply v_const with bt_unit.
      constructor. }
    apply h_op.
    { apply e_app.
      { apply e_value.
        apply v_var.
        apply V2_resume. }
      apply e_value.
      apply v_const with bt_char.
      apply "000"%char. }
    apply h_return.
    { apply e_value.
      apply v_var.
      apply VZ. } }
Defined.

Example Example_bt (b : Example_base_type) : Example_typ.
Proof.
  apply t_base.
  apply b.
Defined.

Example IO_effect_row : Example_typ.
Proof.
  apply t_row_cons.
  { apply t_effect.
    + apply IO_effect.
    + apply nil. }
  apply 〈〉.
Defined.

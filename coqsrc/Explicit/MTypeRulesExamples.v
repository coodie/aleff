Require Import Utf8.
Require Import Common.MBinder.
Require Import Explicit.MSyntax.
Require Import Explicit.ExplicitKind.
Require Import Explicit.MTypeRules.
Require Import Coq.Strings.Ascii.

Definition Empty_function {X : Type} (e : Empty_set) : X :=
  match e with end.

Notation "∅∅" := (Empty_function).

Example Empty_world : world :=
{|
  w_effect_t := ∅;
  w_eff_op_t := ∅∅;
  w_eff_ar   := ∅∅;
  w_base_t   := ∅;
  w_base_v   := ∅∅
|}.

Notation "W∅" := Empty_world.

Example ew_var {TV:Set} (n:TV) : typ W∅ TV := t_var n.

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

Example guards_operation_example :
  guards_operation (inc (inc (inc ∅))) (inc (inc ∅)) (VS (VZ)).
Proof.
  apply gop_step.
  apply gop_base.
Qed.

Inductive Example_base_type : Set :=
| bt_unit : Example_base_type
| bt_char : Example_base_type.

Inductive Example_effect : Set :=
| IO_effect : Example_effect.

Example IO_effect_operation : Set := inc (inc ∅).

Example getc : IO_effect_operation := VZ. 
Example putc : IO_effect_operation := VS VZ.

Example Example_world : world :=
{|
  w_effect_t := Example_effect;
  w_eff_op_t := λ e, IO_effect_operation;
  w_eff_ar   := λ _, 0;
  w_base_t   := Example_base_type;
  w_base_v   := λ b, match b with | bt_unit => True | bt_char => ascii end
|}.

Notation EW := Example_world.
Example Example_typ := typ EW ∅.
Example Example_program := expr EW ∅ ∅.

(*Coercion t_base : EW.(w_base_t) >-> Example_typ.*)

Definition Example_operation_types : Operation_types EW.
Proof.
  intros TV. simpl.
  intros [] _ op.
  destruct op eqn:op_eqn.
  + apply (t_base (bt_unit:w_base_t EW), t_base (bt_char:w_base_t EW)).
  + apply (t_base (bt_char:w_base_t EW), t_base (bt_unit:w_base_t EW)).
Defined.

Example getc_type : ∀ TV eff,
  Example_operation_types TV eff nil getc = (t_base (bt_unit:w_base_t EW), t_base (bt_char:w_base_t EW)).
Proof.
  intros.
  destruct eff.
  reflexivity.
Qed.

Example print_H : Example_program :=
  e_app
    (v_eff_op (IO_effect:w_effect_t EW) putc)
    (v_const  (bt_char  :w_base_t   EW) "H"%char).

Example IO_zero_handler : handler EW ∅ ∅ IO_effect_operation :=
   h_op _ (e_app (v_var V2_resume) (v_const (bt_unit:w_base_t EW) I))
  (h_op _ (e_app (v_var V2_resume) (v_const (bt_char:w_base_t EW) "000"%char))
  (h_return (v_var VZ)
  )).

Example IO_zero_handler_type : ∀ σ_r,
  σ_r ::[ ∅∅ ] k_type →
  handler_has_type Example_operation_types ∅∅ ∅∅
  IO_effect_operation IO_zero_handler IO_effect σ_r σ_r 〈〉.
Proof.
  intros σ_r H.
  apply (HT_op _ _ _ _ (putc:w_eff_op_t EW IO_effect) nil).
  { apply gop_step.
    apply gop_base. }
  { simpl.
    apply T_App with (t_base (bt_unit:w_base_t EW)).
    { apply H. }
    { apply t_base_kind. }
    { constructor. }
    { simpl.
      apply T_Var.
      { reflexivity. }
      constructor. }
    { apply T_Con; constructor. } }
  apply (HT_op _ _ _ _ (getc:w_eff_op_t EW IO_effect) nil).
  { apply gop_base. }
  { simpl.
    apply T_App with (t_base (bt_char:w_base_t EW)).
    { apply H. }
    { apply t_base_kind. }
    { constructor. }
    { simpl.
      apply T_Var.
      { reflexivity. }
      constructor. }
    { apply T_Con; constructor. } }
  apply HT_return.
  constructor.
  + reflexivity.
  + constructor.
Qed.

Example handle_example : expr EW ∅ ∅ :=
  e_handle (IO_effect:w_effect_t EW) nil
    (e_app
      (v_eff_op (IO_effect:w_effect_t EW) getc)
      (v_const (bt_unit:w_base_t EW) I))
    IO_zero_handler.

Example handle_type_example :
  (Example_operation_types,(∅∅:∅ → typ EW ∅),(∅∅:∅ → kind)) ⊢
    handle_example ∈ t_base (bt_char:w_base_t EW) | 〈〉.
Proof.
  apply T_Handle with (t_base (bt_char:w_base_t EW)).
  { reflexivity. }
  { apply IO_zero_handler_type.
    apply t_base_kind. }
  apply T_App with (t_base (bt_unit:w_base_t EW)).
  { apply t_base_kind. }
  { apply t_base_kind. }
  { constructor.
    { apply t_effect_kind.
      reflexivity. }
    apply empty_effect_kind. }
  { apply T_Op with nil.
    reflexivity. }
  { apply T_Con.
    + reflexivity.
    + repeat(constructor). }
Qed.

Require Import Explicit.MSyntax.
Require Import Explicit.MTypeRules.

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
  eapply req_select.
  { apply row_select_tail.
    apply row_select_head. }
  eapply req_select.
  { apply row_select_head. }
  eapply req_select.
  { apply row_select_head. }
  eapply req_select.
  { apply row_select_tail.
    apply row_select_head. }
  eapply req_refl.
Qed.

Example row_append_example : row_append
  〈ew_var 1; ew_var 2〉 〈ew_var 3; ew_var 4〉
  〈ew_var 1; ew_var 2;  ew_var 3; ew_var 4〉.
Proof.
  repeat(apply row_append_step).
  apply row_append_base.
Qed.
Require Import Utf8.
Require Import Explicit.ExplicitKind.
Require Import Common.MBinder.

Record world : Type :=
  { w_effect_t : Set
  ; w_eff_op_t : w_effect_t → Set
  ; w_base_t   : Set
  ; w_base_v   : w_base_t → Set
  }.

Inductive typ (W : world) (TV : Set) : Set :=
| t_var      : TV → typ W TV
| t_base     : W.(w_base_t) → typ W TV
| t_effect   : W.(w_effect_t) → list (typ W TV) → typ W TV
| t_row_nil  : typ W TV
| t_row_cons : typ W TV → typ W TV → typ W TV
| t_arrow    : typ W TV → typ W TV → typ W TV → typ W TV
| t_forall   : kind → typ W (inc TV) → typ W TV
.

Arguments t_var      [W] [TV].
Arguments t_base     [W] [TV].
Arguments t_effect   [W] [TV].
Arguments t_row_nil  [W] [TV].
Arguments t_row_cons [W] [TV].
Arguments t_arrow    [W] [TV].
Arguments t_forall   [W] [TV].

Notation "σ ==>[ ε ] τ" := (t_arrow σ ε τ) (at level 20).
Notation "〈〉" := t_row_nil.
Notation "〈 x ; .. ; y 〉" :=
  (t_row_cons x .. (t_row_cons y t_row_nil) .. ).
Notation "〈 x , .. , y | z 〉" :=
  (t_row_cons x .. (t_row_cons y z) .. ).


Inductive expr (W : world) (TV : Set) (V : Set) : Type :=
| e_value  : value W TV V → expr W TV V
| e_let    : expr W TV V → expr W TV (inc V) → expr W TV V
| e_app    : expr W TV V → expr W TV V → expr W TV V
| e_tapp   : expr W TV V → typ W TV → expr W TV V
| e_open   : expr W TV V → typ W TV → expr W TV V
| e_handle : ∀ l : W.(w_effect_t),
    list (typ W TV) →
    expr W TV V →
    handler W TV V (W.(w_eff_op_t) l) →
    expr W TV V
with value (W : world) (TV : Set) (V : Set) : Type :=
| v_var    : V → value W TV V
| v_const  : ∀ b : W.(w_base_t), W.(w_base_v) b → value W TV V
| v_eff_op : ∀ l : W.(w_effect_t), W.(w_eff_op_t) l → value W TV V
| v_lam    : typ W TV → expr W TV (inc V) → typ W TV → value W TV V
| v_tlam   : kind → value W (inc TV) V → value W TV V
with handler (W : world) (TV : Set) (V : Set) : Set → Type :=
| h_return : expr W TV (inc V) → handler W TV V Empty_set
| h_op     : ∀ Op : Set,
    expr W TV (inc2_h V) →
    handler W TV V Op →
    handler W TV V (inc Op)
.

Arguments e_value  [W] [TV] [V].
Arguments e_let    [W] [TV] [V].
Arguments e_app    [W] [TV] [V].
Arguments e_tapp   [W] [TV] [V].
Arguments e_open   [W] [TV] [V].
Arguments e_handle [W] [TV] [V].

Arguments v_var    [W] [TV] [V].
Arguments v_const  [W] [TV] [V].
Arguments v_eff_op [W] [TV] [V].
Arguments v_lam    [W] [TV] [V].
Arguments v_tlam   [W] [TV] [V].

Arguments h_return [W] [TV] [V].
Arguments h_op     [W] [TV] [V].

Coercion e_value : value >-> expr.

Definition tsubst_t {W : world} {TV : Set} :
  typ W (inc TV) → typ W TV → typ W TV.
Admitted.

Definition tsubst_e {W : world} {TV V : Set} :
  expr W (inc TV) V → typ W TV → expr W TV V.
Admitted.

Definition tsubst_v {W : world} {TV V : Set} :
  value W (inc TV) V → typ W TV → value W TV V.
Admitted.

Definition subst_e {W : world} {TV V : Set} :
  expr W TV (inc V) → value W TV V → expr W TV V.
Admitted.

Definition subst_v {W : world} {TV V : Set} :
  value W TV (inc V) → value W TV V → value W TV V.
Admitted.

Definition subst_e2_h {W : world} {TV V : Set} :
  expr W TV (inc2_h V) → value W TV V → value W TV V → expr W TV V.
Admitted.

Definition subst_v2 {W : world} {TV V : Set} :
  value W TV (inc2_h V) → value W TV V → value W TV V → value W TV V.
Admitted.
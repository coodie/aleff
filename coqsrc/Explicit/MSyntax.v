Require Import Utf8.
Require Import Explicit.ExplicitKind.
Require Import Common.MBinder.

Record world : Type :=
  { w_effect_t : Set
  ; w_eff_op_t : w_effect_t → Set
  ; w_base_t   : Set
  ; w_base_v   : w_base_t → Set
  ; w_primop   : Set
  }.

Inductive typ (W : world) (TV : Set) : Set :=
| t_var      : TV → typ W TV
| t_base     : W.(w_base_t) → typ W TV
| t_effect   : W.(w_effect_t) → typ W TV
| t_row_nil  : typ W TV
| t_row_cons : typ W TV → typ W TV → typ W TV
| t_arrow    : typ W TV → typ W TV → typ W TV → typ W TV
| t_forall   : kind → typ W (inc TV) → typ W TV
.

Inductive expr (W : world) (TV : Set) (V : Set) : Type :=
| e_value  : value W TV V → expr W TV V
| e_let    : expr W TV V → expr W TV (inc V) → expr W TV V
| e_app    : expr W TV V → expr W TV V → expr W TV V
| e_tapp   : expr W TV V → typ W TV → expr W TV V
| e_open   : expr W TV V → typ W TV → expr W TV V
| e_handle : ∀ l : W.(w_effect_t),
    expr W TV V →
    handler W TV V (W.(w_eff_op_t) l) →
    expr W TV V
| e_primop : W.(w_primop) → list (value W TV V) → expr W TV V
with value (W : world) (TV : Set) (V : Set) : Type :=
| v_var    : V → value W TV V
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
Require Import Utf8.
Require Import Common.MBinder.
Require Import Explicit.MSyntax.
Require Import Explicit.ExplicitKind.

(* 2329 〈  232a 〉 *)

Reserved Notation "τ ::[ Δ ] k" (at level 60).

Inductive has_kind {W : world} {TV : Set} (Δ : TV → kind) : typ W TV → kind → Prop :=
| var_kind : ∀ (α' : TV),
    @t_var W TV α' ::[Δ] Δ α'
| t_effect_kind : ∀ (e : W.(w_effect_t)) e_args,
    length e_args = W.(w_eff_ar) e →
    @t_effect W TV e e_args ::[Δ] k_effect
| empty_effect_kind : 
    @t_row_nil W TV ::[Δ] k_eff_row
| effect_extension_kind : ∀ (l ε : typ W TV),
      l   ::[Δ] k_effect  →
      ε   ::[Δ] k_eff_row →
    〈l|ε〉 ::[Δ] k_eff_row 

| t_base_kind : ∀ (τ : W.(w_base_t)),
    @t_base W TV τ ::[Δ] k_type
| functions_kind : ∀ (τ₁ τ₂ ε : typ W TV),
    τ₁ ::[Δ] k_type    →
    ε  ::[Δ] k_eff_row →
    τ₂ ::[Δ] k_type    →
    τ₁ ==>[ε] τ₂ ::[Δ] k_type

(* t_app is removed
| type_contructor_kind : ∀ (c τ : typ W TV) (k₁ k₂:kind),
   τ ::[Δ] k₁ →
   c ::[Δ] k_arrow k₁ k₂ →
   t_app c τ ::[Δ] k₂
*)

where "τ ::[ Δ ] k" := (@has_kind _ _ Δ τ k).

Theorem k_eff_row_ind {W : world} {TV : Set} : ∀ (P : typ W TV → Prop) (Δ : TV → kind),
  (∀ (α' : TV), P (t_var α')) →
  (P (@t_row_nil W TV)) →
  (∀ (l ε : typ W TV), l ::[Δ] k_effect → ε ::[Δ] k_eff_row → P ε → P 〈l|ε〉) → 
  ∀ ε : typ W TV, ε ::[Δ] k_eff_row → P ε.
Proof.
  intros P Δ base_var base_nil step.
  induction ε ;
  intros H ; inversion H.
  + apply base_var.
  + apply base_nil.
  + subst. clear IHε1.
    assert(IH:= IHε2 P Δ base_var base_nil step H3).
    apply (step ε1 ε2 H2 H3 IH).
Qed.

Reserved Notation "ε₁ ≅[ Δ ] ε₂" (at level 40).

Inductive row_equivalence {W : world} {TV : Set} (Δ : TV → kind) : typ W TV → typ W TV → Prop :=
| req_refl : ∀ (ε : typ W TV), ε ::[Δ] k_eff_row →
    ε ≅[Δ] ε
| req_swap : ∀ (l₁ l₂ ε: typ W TV),
    l₁ ::[Δ] k_effect →
    l₂ ::[Δ] k_effect →
    ε  ::[Δ] k_eff_row →
    〈l₁ , l₂ | ε〉 ≅[Δ] 〈l₂ , l₁ | ε〉

| req_head : ∀ (ε₁ ε₂ l: typ W TV),
  l ::[Δ] k_effect →
  ε₁ ≅[Δ] ε₂ →
  〈l | ε₁〉 ≅[Δ] 〈l | ε₂〉
| req_trans : ∀ (ε₁ ε₂ ε₃: typ W TV),
  ε₁ ::[Δ] k_eff_row →
  ε₂ ::[Δ] k_eff_row →
  ε₃ ::[Δ] k_eff_row →
  ε₁ ≅[Δ] ε₂ → ε₂ ≅[Δ] ε₃ → ε₁ ≅[Δ] ε₃

where "ε₁ ≅[ Δ ] ε₂" := (@row_equivalence _ _ Δ ε₁ ε₂).
Notation "ε₁ ≆[ Δ ] ε₂" := (~(@row_equivalence _ _ Δ ε₁ ε₂)) (at level 40).

Lemma uneq_label {W : world} {TV : Set} (c c': W.(w_effect_t)) (args args': list (typ W TV)) (Δ : TV → kind): 
  c ≠ c' →
  t_effect c args ≆[Δ] t_effect c' args'.
Proof.
  intros neq equiv.
  inversion equiv.
  + apply (neq H).
  + admit.
Admitted.

Definition env {W:world} {TV : Set} (V:Set) : Set := V → typ W TV.

Example Empty_function {X : Type} (e : Empty_set) : X := 
  match e with end.

Notation "∅" := (Empty_function).

Definition env_ext {W:world} {TV : Set} {V :Set}
 (Γ : env V) (τ : typ W TV) (x : inc V) : typ W TV :=
  match x with
  | VZ   => τ
  | VS y => Γ y
  end.

Notation "Γ ',+' τ" := (@env_ext _ _ _ Γ τ) (at level 45, left associativity).

Reserved Notation "Γ ';' Δ '⊢' t '∈' τ '|' ε" (at level 50).

Inductive has_type {W:world} {TV : Set} {V : Set} (Γ : @env W TV V) (Δ : TV → kind): 
  expr W TV V → typ W TV → typ W TV → Prop :=
| T_Req : ∀ (e : expr W TV V) (τ ε₁ ε₂:typ W TV),
    ε₁ ≅[Δ] ε₂ →
    Γ ; Δ ⊢ e ∈ τ | ε₁ →
    Γ ; Δ ⊢ e ∈ τ | ε₂ 

| T_Con : ∀ (x : V) (ε : typ W TV) (b : W.(w_base_t)) (v : W.(w_base_v) b),
    ε ::[Δ] k_eff_row →
    Γ ; Δ ⊢ v_const b v ∈ t_base b | ε
| T_Var : ∀ (x : V) (ε : typ W TV),
    ε ::[Δ] k_eff_row →
    Γ ; Δ  ⊢ v_var x ∈ (Γ x) | ε

| T_Lam : ∀ (e : expr W TV (inc V)) (σ σ₁ ε ε' STH: typ W TV),
    σ  ::[Δ] k_type →
    σ₁ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    ε' ::[Δ] k_eff_row →
    Γ,+ σ₁ ; Δ  ⊢ e ∈ σ | ε → 
    Γ ; Δ  ⊢ v_lam σ₁ e ε ∈ σ₁ ==>[ε] σ | ε'

| T_App : ∀ (e₁ e₂ : expr W TV V) (σ σ₂ ε : typ W TV),
    σ  ::[Δ] k_type →
    σ₂ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    Γ ; Δ  ⊢ e₁ ∈ σ₂ ==>[ε] σ | ε →
    Γ ; Δ  ⊢ e₂ ∈ σ₂ | ε →
    Γ ; Δ  ⊢ e_app e₁ e₂ ∈ σ | ε

| T_Let : ∀ (e₁ : expr W TV V) (e₂ : expr W TV (inc V)) (σ σ₂ ε : typ W TV),  
    σ  ::[Δ] k_type →
    σ₂ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    Γ ; Δ  ⊢ e₁ ∈ σ | ε →
    Γ,+ σ ; Δ  ⊢ e₂ ∈ σ₂ | ε →
    Γ ; Δ  ⊢ e_let e₁ e₂ ∈ σ | ε

(* FILL IN HERE *)

where "Γ ; Δ '⊢' t '∈' τ '|' ε" := (@has_type _ _ _ Γ Δ t τ ε).


Require Import Utf8.
Require Import Common.MBinder.
Require Import Explicit.MSyntax.
Require Import Explicit.ExplicitKind.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Lists.List.

(** ** Row equivalence *)

Inductive row_append {W : world} {TV : Set} : typ W TV → typ W TV → typ W TV → Prop :=
| row_append_base : ∀ (ε         : typ W TV), row_append 〈〉 ε  ε
| row_append_step : ∀ (l ε ε' εε': typ W TV), row_append  ε ε' εε' → row_append 〈l|ε〉 ε' 〈l|εε'〉.

Definition closed_row {W : world} {TV : Set} (ε : typ W TV) : Prop := row_append ε 〈〉 ε.

Inductive row_select {W : world} {TV : Set} : typ W TV → typ W TV → typ W TV → Prop :=
| row_select_head : ∀ (l ε: typ W TV), row_select l 〈l|ε〉 ε
| row_select_tail : ∀ (l l' ε ε': typ W TV), row_select l ε ε' → row_select l 〈l'|ε〉 〈l'|ε'〉.

Lemma row_select_arg2_cons {W : world} {TV : Set} : ∀ (l ε ε'': typ W TV),
  row_select l ε ε'' →
  ∃ (l' ε': typ W TV), ε = 〈l'|ε'〉.
Proof.
  intros.
  inversion H; subst.
  + exists l. exists ε''. auto.
  + exists l'. exists ε0. auto.
Qed.

Lemma row_select_comm {W : world} {TV : Set} : ∀ (l l' ε ε' ε'' : typ W TV),
  row_select l  ε  ε'  →
  row_select l' ε' ε'' →
  ∃ ε1,
  row_select l' ε  ε1  ∧
  row_select l  ε1 ε''.
Proof.
  intros l l' ε ε' ε''.
  induction ε''; intros.
  + inversion H0. subst. clear H0.
    inversion H; subst.
    - eapply ex_intro.
      split; [|apply row_select_head].
      apply row_select_tail.
      apply row_select_head.
    - eapply ex_intro.
      split; [|apply row_select_head].
      inversion H3. subst.
      apply row_select_head.
  + admit.
  + admit.
  + admit.
  + Admitted.  

Reserved Notation "ε₁ ≅ ε₂" (at level 40).

Inductive row_equivalence {W : world} {TV : Set} : relation (typ W TV) :=
| req_refl : ∀ (ε : typ W TV),
    ε  ≅ ε
| req_select : ∀ (l ε₁ ε₁' ε₂': typ W TV),
    row_select l ε₁ ε₁' →
    ε₁' ≅ ε₂' →
    ε₁  ≅ 〈l|ε₂'〉

where "ε₁ ≅ ε₂" := (@row_equivalence _ _ ε₁ ε₂).
Notation "ε₁ ≆ ε₂" := (¬(@row_equivalence _ _ ε₁ ε₂)) (at level 40).

Lemma req_select_inv {W : world} {TV : Set} : ∀ (l ε₁ ε₂': typ W TV),
  ε₁  ≅ 〈l|ε₂'〉 →
  ∃ (ε₁': typ W TV),
  row_select l ε₁ ε₁' ∧
  ε₁' ≅ ε₂'.
Proof.
  intros l ε₁ ε₂' H.
  inversion H; subst.
  + exists ε₂'. split.
    - apply row_select_head.
    - apply req_refl.
  + exists ε₁'. split;
    assumption.
Qed.

Lemma req_head {W : world} {TV : Set} : ∀ (ε₁ ε₂ l: typ W TV),
  ε₁ ≅ ε₂ →
  〈l | ε₁〉 ≅ 〈l | ε₂〉.
Proof.
  intros.
  apply req_select with ε₁.
  + constructor.
  + assumption.
Qed.

Lemma req_swap {W : world} {TV : Set} : ∀ (l₁ l₂ ε: typ W TV),
    〈l₁ , l₂ | ε〉 ≅ 〈l₂ , l₁ | ε〉.
Proof.
  intros.
  eapply req_select.
  + eapply row_select_tail.
    apply row_select_head.
  + apply req_refl.
Qed.

Lemma req_select' {W : world} {TV : Set} : ∀ (l ε₁ ε₁' ε₂ ε₂': typ W TV),
  ε₁' ≅ ε₂' →
  row_select l ε₁ ε₁' →
  row_select l ε₂ ε₂' →
  ε₁  ≅ ε₂.
Proof.
Admitted.

Lemma req_symm {W : world} {TV : Set} : ∀ (ε₁ ε₂: typ W TV),
  ε₁ ≅ ε₂ → ε₂ ≅ ε₁.
Proof.
  intros.
  induction H.
  + constructor.
  + eapply (req_select' l _ ε₂').
    - apply IHrow_equivalence.
    - subst.
      apply row_select_head.
    - assumption.
Qed.

Lemma req_trans {W : world} {TV : Set} : ∀ (ε₁ ε₂ ε₃: typ W TV),
  ε₁ ≅ ε₂ → ε₂ ≅ ε₃ → ε₁ ≅ ε₃.
Proof.
  intros ε₁ ε₂ ε₃ H.
  generalize dependent ε₃.
  induction H.
  { tauto. }
  intros.
  apply req_symm in H1.
  destruct (req_select_inv _ _ _ H1) as [ε₃' [ε₃'_def ε₃'_prop]].
  assert (IH := IHrow_equivalence _ (req_symm _ _ ε₃'_prop)).
  apply (req_select' l _ ε₁' _ ε₃');
  assumption.
Qed.

Lemma uneq_label {W : world} {TV : Set} (c c': W.(w_effect_t)) (args args': list (typ W TV)) (Δ : TV → kind): 
  c ≠ c' →
  t_effect c args ≆ t_effect c' args'.
Proof.
  intros neq equiv.
  inversion equiv; subst.
  + apply neq.
    reflexivity.
Qed.

Instance row_equivalence_equivalence {W : world} {TV : Set} :
  Equivalence (@row_equivalence W TV).
Proof.
  split.
  + constructor.
  + unfold Symmetric. apply req_symm.
  + unfold Transitive. apply req_trans.
Qed.

(** ** Proper type rules **)

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

Definition inc_type {W:world} {TV : Set} (τ : typ W TV) : typ W (inc TV).
Admitted.

Definition inc_env {W:world} {TV : Set} {V :Set} (Γ : @env W TV V) (x : V) : typ W (inc TV) :=
  inc_type (Γ x).

Definition kinding_env_ext {TV : Set}
  (Δ:TV → kind) (k : kind) (α : inc TV) : kind :=
  match α with
  | VZ    => k
  | VS α' => Δ α'
  end.

Notation "Δ ',*' k" := (@kinding_env_ext _ Δ k) (at level 45, left associativity).

Reserved Notation "Γ ';;' Δ '⊢' t '∈' τ '|' ε" (at level 50).

Definition Φ {W:world} (l: W.(w_effect_t)) : (W.(w_eff_op_t) l) → typ W Empty_set.
Admitted.

Inductive has_type {W:world} {TV : Set} {V : Set} (Γ : @env W TV V) (Δ : TV → kind): 
  expr W TV V → typ W TV → typ W TV → Prop :=
| T_Req : ∀ (e : expr W TV V) (τ ε₁ ε₂:typ W TV),
    ε₁ ≅ ε₂ →
    Γ ;; Δ ⊢ e ∈ τ | ε₁ →
    Γ ;; Δ ⊢ e ∈ τ | ε₂

| T_Con : ∀ (x : V) (ε : typ W TV) (b : W.(w_base_t)) (v : W.(w_base_v) b),
    ε ::[Δ] k_eff_row →
    Γ ;; Δ ⊢ v_const b v ∈ t_base b | ε
| T_Var : ∀ (x : V) (ε : typ W TV),
    ε ::[Δ] k_eff_row →
    Γ ;; Δ ⊢ v_var x ∈ (Γ x) | ε

| T_Lam : ∀ (e : expr W TV (inc V)) (σ σ₁ ε ε': typ W TV),
    σ  ::[Δ] k_type →
    σ₁ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    ε' ::[Δ] k_eff_row →
    Γ,+ σ₁ ;; Δ  ⊢ e ∈ σ | ε →
    Γ ;; Δ ⊢ v_lam σ₁ e ε ∈ σ₁ ==>[ε] σ | ε'

| T_App : ∀ (e₁ e₂ : expr W TV V) (σ σ₂ ε : typ W TV),
    σ  ::[Δ] k_type →
    σ₂ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    Γ ;; Δ ⊢ e₁ ∈ σ₂ ==>[ε] σ | ε →
    Γ ;; Δ ⊢ e₂ ∈ σ₂ | ε →
    Γ ;; Δ ⊢ e_app e₁ e₂ ∈ σ | ε

| T_TLam : ∀ (e: value W (inc TV) V) (σ: typ W (inc TV)) (ε: typ W TV) (k :kind),
    σ  ::[Δ,* k] k_type  →
    ε  ::[Δ] k_eff_row →
    inc_env Γ ;; (Δ,* k)  ⊢ e ∈ σ | inc_type ε →
    Γ ;; Δ ⊢ v_tlam k e ∈ t_forall k σ | ε

| T_TApp : ∀ (e : expr W TV V) (σ₁ ε : typ W TV) (σ : typ W (inc TV)) (k :kind),
    σ₁ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    σ  ::[Δ,* k] k_type →
    Γ ;; Δ ⊢ e ∈ t_forall k σ | ε →
    Γ ;; Δ ⊢ e_tapp e σ₁ ∈ tsubst_t σ σ₁ | ε

| T_Open : ∀ (e : expr W TV V) (σ₁ σ₂ ls ε lsε ε' : typ W TV),
    ls  ::[Δ] k_eff_row →
    ε   ::[Δ] k_eff_row →
    σ₁  ::[Δ] k_type →
    σ₂  ::[Δ] k_type →
    ε'  ::[Δ] k_eff_row →
    row_append ls ε lsε →
    Γ ;; Δ ⊢ e ∈ σ₁ ==>[ls] σ₂ | ε' →
    Γ ;; Δ ⊢ e_open e ε ∈ σ₁ ==>[lsε] σ₂ | ε'

| T_Handle : ∀ 
    (l : W.(w_effect_t))
    (args : list (typ W TV))
    (e : expr W TV V)
    (h : handler W TV V (W.(w_eff_op_t) l))
    (σ_r σ ε : typ W TV),
    length args = W.(w_eff_ar) l →
    handler_has_type Γ Δ (W.(w_eff_op_t) l) h σ_r σ ε →
    Γ ;; Δ ⊢ e ∈ σ_r | 〈t_effect l args|ε〉 →
    Γ ;; Δ ⊢ e_handle l args e h ∈ σ | ε

| T_Let : ∀ (e₁ : expr W TV V) (e₂ : expr W TV (inc V)) (σ σ₂ ε : typ W TV),  
    σ  ::[Δ] k_type →
    σ₂ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    Γ ;; Δ  ⊢ e₁ ∈ σ | ε →
    Γ,+ σ ;; Δ  ⊢ e₂ ∈ σ₂ | ε →
    Γ ;; Δ  ⊢ e_let e₁ e₂ ∈ σ | ε

with handler_has_type {W:world} {TV : Set} {V : Set} (Γ : @env W TV V) (Δ : TV → kind):
  forall (Op : Set), handler W TV V Op → typ W TV → typ W TV → typ W TV → Prop :=

| HT_return : forall (l : W.(w_effect_t)) (e : expr W TV (inc V)) (σ_r σ ε: typ W TV),
   Γ,+ σ_r ;; Δ ⊢ e ∈ σ | ε →
   handler_has_type Γ Δ Empty_set (h_return e) σ_r σ ε
(* FILL IN HERE *)

where "Γ ';;' Δ '⊢' t '∈' τ '|' ε" := (@has_type _ _ _ Γ Δ t τ ε).

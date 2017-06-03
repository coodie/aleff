Require Import Utf8.
Require Import Common.MBinder.
Require Import Explicit.MSyntax.
Require Import Explicit.ExplicitKind.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.

(* temporary definitions from MSyntax.v *)

Definition tmap_t {W : world} {TV TV' : Set} (f : TV → TV') (t : typ W TV) : typ W TV'.
Admitted.

Notation tshift_t := (tmap_t (@VS _)).

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

Lemma row_select_comm {W : world} {TV : Set} : ∀ (l ε  ε' l' ε'': typ W TV) ,
  row_select l  ε  ε'  →
  row_select l' ε' ε'' →
  ∃ ε1,
  row_select l' ε  ε1  ∧
  row_select l  ε1 ε''.
Proof.
  induction ε ; intros ; inversion H ; subst ; clear IHε1.
  + exists 〈ε1 | ε'' 〉. split.
    - constructor. exact H0.
    - constructor.
  +  inversion H0 ; subst.
      - exists ε2. split. 
        * constructor. 
        * exact H5.
      - assert (IH := IHε2 l ε'0 l' ε' H5 H6). 
        destruct IH. destruct H1.
         exists 〈ε1 | x 〉. split. 
        * constructor. exact H1.
        * constructor. exact H2. 
Qed.

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

Definition env_ext  {W : world} {TV : Set} {V : Set}
 (Γ : env V) (τ : typ W TV) (x : inc V) : typ W TV :=
  match x with
  | VZ   => τ
  | VS y => Γ y
  end.

Definition env_ext2 {W : world} {TV : Set} {V : Set}
  (Γ : env V) (τϱ: (typ W TV * typ W TV)) (x : inc2_h V) : typ W TV :=
  let (τ,ϱ) := τϱ in
  match x with
  | V2_arg    => τ
  | V2_resume => ϱ
  | V2S y     => Γ y
  end.

Notation "Γ ',+'  τ"  := (@env_ext  _ _ _ Γ τ ) (at level 45, left associativity).
Notation "Γ ',++' τϱ" := (@env_ext2 _ _ _ Γ τϱ) (at level 45, left associativity).

Definition tshift_env {W:world} {TV : Set} {V :Set} (Γ : @env W TV V) (x : V) : typ W (inc TV) :=
  (compose tshift_t Γ) x.

Definition kinding_env_ext {TV : Set}
  (Δ:TV → kind) (k : kind) (α : inc TV) : kind :=
  match α with
  | VZ    => k
  | VS α' => Δ α'
  end.

Notation "Δ ',*' k" := (@kinding_env_ext _ Δ k) (at level 45, left associativity).

Definition Operation_types (W:world) := 
  ∀ (TV:Set) (l:W.(w_effect_t)), (list (typ W TV)) → (W.(w_eff_op_t) l) → 
    (typ W TV * typ W TV).

Notation "∅"  := Empty_set.

Inductive guards_operation : ∀ T, Set → T → Prop  :=
  | gop_base : ∀ T, guards_operation _ (inc ∅) (VZ:inc T)
  | gop_step : ∀ T (G_Op:Set) (op:inc T), 
      guards_operation _      G_Op      op →
      guards_operation _ (inc G_Op) (VS op).

Reserved Notation "ΦΓΔ '⊢' t '∈' τ '|' ε" (at level 50).

Inductive has_type {W:world} {TV : Set} {V : Set}
  (Φ : Operation_types W) 
  (Γ : @env W TV V) (Δ : TV → kind)
: 
  expr W TV V → typ W TV → typ W TV → Prop :=
| T_Req : ∀ (e : expr W TV V) (τ ε₁ ε₂:typ W TV),
    ε₁ ≅ ε₂ →
    (Φ,Γ,Δ) ⊢ e ∈ τ | ε₁ →
    (Φ,Γ,Δ) ⊢ e ∈ τ | ε₂

| T_Con : ∀ (σ ε : typ W TV) (b : W.(w_base_t)) (v : W.(w_base_v) b),
    σ = t_base b →
    ε ::[Δ] k_eff_row →
    (Φ,Γ,Δ) ⊢ v_const b v ∈ σ | ε
| T_Op : ∀  (ε σ:typ W TV) (l : W.(w_effect_t)) (op: W.(w_eff_op_t) l) (args : list (typ W TV)),
    σ = (let (σ₁,σ₂) := Φ TV l args op in σ₁ ==>[〈t_effect l args〉] σ₂) →
    (Φ,Γ,Δ)  ⊢ v_eff_op l op ∈ σ | ε
| T_Var : ∀ (x: V) (σ ε : typ W TV),
    σ = Γ x →
    ε ::[Δ] k_eff_row →
    (Φ,Γ,Δ) ⊢ v_var x ∈ σ | ε

| T_Lam : ∀ (e : expr W TV (inc V)) (σ σ₁ ε ε': typ W TV),
    σ  ::[Δ] k_type →
    σ₁ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    ε' ::[Δ] k_eff_row →
    (Φ,Γ,+σ₁,Δ) ⊢ e ∈ σ | ε →
    (Φ,Γ    ,Δ) ⊢ v_lam σ₁ e ε ∈ σ₁ ==>[ε] σ | ε'

| T_App : ∀ (e₁ e₂ : expr W TV V) (σ σ₂ ε : typ W TV),
    σ  ::[Δ] k_type →
    σ₂ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    (Φ,Γ,Δ) ⊢ e₁ ∈ σ₂ ==>[ε] σ | ε →
    (Φ,Γ,Δ) ⊢ e₂ ∈ σ₂ | ε →
    (Φ,Γ,Δ) ⊢ e_app e₁ e₂ ∈ σ | ε

| T_TLam : ∀ (e: value W (inc TV) V) (σ: typ W (inc TV)) (ε: typ W TV) (k :kind),
    σ  ::[Δ,* k] k_type  →
    ε  ::[Δ] k_eff_row →
    (Φ,tshift_env Γ,Δ,* k) ⊢ e ∈ σ | tshift_t ε →
    (Φ,           Γ,Δ    ) ⊢ v_tlam k e ∈ t_forall k σ | ε

| T_TApp : ∀ (e : expr W TV V) (σ₁ ε : typ W TV) (σ : typ W (inc TV)) (k :kind),
    σ₁ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    σ  ::[Δ,* k] k_type →
    (Φ,Γ,Δ) ⊢ e ∈ t_forall k σ | ε →
    (Φ,Γ,Δ) ⊢ e_tapp e σ₁ ∈ tsubst_t σ σ₁ | ε

| T_Open : ∀ (e : expr W TV V) (σ₁ σ₂ ls ε lsε ε' : typ W TV),
    ls  ::[Δ] k_eff_row →
    ε   ::[Δ] k_eff_row →
    σ₁  ::[Δ] k_type →
    σ₂  ::[Δ] k_type →
    ε'  ::[Δ] k_eff_row →
    row_append ls ε lsε →
    (Φ,Γ,Δ) ⊢ e ∈ σ₁ ==>[ls] σ₂ | ε' →
    (Φ,Γ,Δ) ⊢ e_open e ε ∈ σ₁ ==>[lsε] σ₂ | ε'

| T_Handle : ∀ 
    (l : W.(w_effect_t))
    (args : list (typ W TV))
    (e : expr W TV V)
    (h : handler W TV V (W.(w_eff_op_t) l))
    (σ_r σ ε : typ W TV),
    length args = W.(w_eff_ar) l →
    handler_has_type Φ Γ Δ (W.(w_eff_op_t) l) h l σ_r σ ε →
    (Φ,Γ,Δ) ⊢ e ∈ σ_r | 〈t_effect l args|ε〉 →
    (Φ,Γ,Δ) ⊢ e_handle l args e h ∈ σ | ε

| T_Let : ∀ (e₁ : expr W TV V) (e₂ : expr W TV (inc V)) (σ σ₂ ε : typ W TV),  
    σ  ::[Δ] k_type →
    σ₂ ::[Δ] k_type →
    ε  ::[Δ] k_eff_row →
    (Φ,Γ    ,Δ) ⊢ e₁ ∈ σ | ε →
    (Φ,Γ,+ σ,Δ) ⊢ e₂ ∈ σ₂ | ε →
    (Φ,Γ    ,Δ) ⊢ e_let e₁ e₂ ∈ σ | ε

with handler_has_type {W:world} {TV : Set} {V : Set}
  (Φ : Operation_types W)
  (Γ : @env W TV V) (Δ : TV → kind)
:
  ∀ (Op : Set), handler W TV V Op → W.(w_effect_t) → 
  typ W TV → typ W TV → typ W TV → Prop :=

| HT_return : ∀ (l : W.(w_effect_t)) (e : expr W TV (inc V)) (σ_r σ ε: typ W TV),
   (Φ, Γ,+ σ_r , Δ) ⊢ e ∈ σ | ε →
   handler_has_type Φ Γ Δ ∅ (h_return e) l σ_r σ ε

| HT_op : ∀ (l : W.(w_effect_t)),
   let Op := W.(w_eff_op_t) l in ∀
   (op : Op)
   (args : list (typ W TV))
   (G_Op : Set)
   (h : handler W TV V G_Op)
   (σ_r σ ε: typ W TV) (e_i: expr W TV (inc2_h V)),
   guards_operation Op (inc G_Op) op →
   (Φ, Γ,++ ( let (σ₁,σ₂) := Φ TV l args op in 
     (σ₁,σ₂ ==>[ε] σ)),
     Δ) ⊢ e_i ∈ σ | ε →
   handler_has_type Φ Γ Δ      G_Op                 h  l σ_r σ ε →
   handler_has_type Φ Γ Δ (inc G_Op) (h_op G_Op e_i h) l σ_r σ ε

where "ΦΓΔ '⊢' t '∈' τ '|' ε" := (@has_type _ _ _ 
  (fst(fst ΦΓΔ)) (snd(fst ΦΓΔ)) (snd ΦΓΔ) t τ ε).

Require Import Utf8.
Require Import Common.MBinder.
Require Import Explicit.MSyntax.
Require Import Explicit.ExplicitKind.

(* 2329 〈  232a 〉  2245 ≅ *)

Reserved Notation "τ ':::' k" (at level 40).

Inductive has_kind {W : world} {TV : Set} : typ W TV -> kind -> Prop :=
| t_effect_kind : forall (e : W.(w_effect_t)) STH, 
    @t_effect W TV e STH ::: k_effect
| empty_effect_kind : 
    @t_row_nil W TV ::: k_eff_row
| effect_extension_kind : forall (l ε : typ W TV),
    l ::: k_effect  ->
    ε ::: k_eff_row ->
    〈l|ε〉 ::: k_eff_row 

| t_base_kind : forall (τ : W.(w_base_t)),
    @t_base W TV τ ::: k_type
| functions_kind : forall (τ_1 τ_2 ε : typ W TV),
    τ_1 ::: k_type    ->
    ε   ::: k_eff_row ->
    τ_2 ::: k_type    ->
    t_arrow τ_1 ε τ_2 ::: k_type

(* t_app is removed
| type_contructor_kind : forall (c τ : typ W TV) (k_1 k_2:kind),
   τ ::: k_1 ->
   c ::: k_arrow k_1 k_2 ->
   t_app c τ ::: k_2
*)

where "τ ':::' k" := (@has_kind _ _ τ k).


Theorem k_eff_row_ind {W : world} {TV : Set} : forall (P : typ W TV -> Prop),
  (P (@t_row_nil W TV)) ->
  (forall (l ε : typ W TV), l ::: k_effect -> ε ::: k_eff_row -> P ε -> P 〈l|ε〉) -> 
  forall ε : typ W TV, ε ::: k_eff_row -> P ε.
Proof.
  intros P base step.
  induction ε ;
  intros H ; inversion H.
  + apply base.
  + subst. clear IHε1.
    assert(IH:= IHε2 P base step H3).
    apply (step ε1 ε2 H2 H3 IH).
Qed.

(* maybe not needed
Theorem k_eff_row_ind2 {W : world} {TV : Set} : forall (P : typ W TV -> typ W TV -> Prop),
  (forall (e:typ W TV), e ::: k_eff_row -> P (@t_row_nil W TV) e) ->
  (forall (e:typ W TV), e ::: k_eff_row -> P e (@t_row_nil W TV)) ->
  (forall (l l' e e':typ W TV), l ::: k_effect -> l' ::: k_effect ->
    e ::: k_eff_row -> e' ::: k_eff_row -> P e e' -> P 〈l|e〉 〈l'|e'〉) ->
  forall (e e':typ W TV), e ::: k_eff_row -> e' ::: k_eff_row -> P e e'.
Proof.
  intros P lbase rbase step.
  induction e;
  intros e' H; inversion H; generalize dependent e'.
  + apply lbase.
  + subst. clear IHe1.
    assert(IH:= IHe2 P lbase rbase step). clear IHe2.
    intros e' H'.
    destruct e'; inversion H'.
    - apply rbase. assumption.
    - subst.
      apply step; try(assumption).
      apply IH; assumption.
Qed. *)

Reserved Notation "ε_1 '≅' ε_2" (at level 40).

Inductive row_equivalence {W : world} {TV : Set} : typ W TV -> typ W TV -> Prop :=
| req_refl : forall (ε : typ W TV), ε ::: k_eff_row ->
    ε ≅ ε
| req_swap : forall (l_1 l_2 ε: typ W TV),
    l_1 ::: k_effect ->
    l_2 ::: k_effect ->
    ε   ::: k_eff_row ->
    (* ~(l_1 ≅ l_2) -> *) (* not strictly positive occurrence *)
    〈l_1 , l_2 | ε〉 ≅ 〈l_2 , l_1 | ε〉

| req_head : forall (ε_1 ε_2 l: typ W TV),
  l ::: k_effect ->
  ε_1 ≅ ε_2 ->
  〈l | ε_1〉 ≅ 〈l | ε_2〉
| req_trans : forall (ε_1 ε_2 ε_3: typ W TV),
  ε_1 ::: k_eff_row ->
  ε_2 ::: k_eff_row ->
  ε_3 ::: k_eff_row ->
  ε_1 ≅ ε_2 -> ε_2 ≅ ε_3 -> ε_1 ≅ ε_3

where "ε_1 '≅' ε_2" := (@row_equivalence _ _ ε_1 ε_2).
Notation "ε_1 ≆ ε_2" := (~(@row_equivalence _ _ ε_1 ε_2)) (at level 40).

(* t_app removed
Lemma uneq_label {W : world} {TV : Set} : forall (c c' ε ε' : typ W TV),
  (exists k k', c  ::: k_arrow k k') ->
  (exists k k', c' ::: k_arrow k k') ->
  ε  ::: k_eff_row ->
  ε' ::: k_eff_row ->
  c <> c' ->
  t_app c ε ≆  t_app ε'.
*)

(* based od SimpleTypes.v *)
Definition env {W:world} {TV : Set} (V:Set) : Set := V → typ W TV.

(*
Definition env_empty (x : Empty_set) : tp :=
  match x with end.
Notation "∅" := (env_empty).
*)

Definition env_ext {W:world} {TV : Set} {V :Set}
 (Γ : env V) (τ : typ W TV) (x : inc V) : typ W TV :=
  match x with
  | VZ   => τ
  | VS y => Γ y
  end.

Notation "Γ ',+' τ" := (@env_ext _ _ _ Γ τ) (at level 45, left associativity).

Reserved Notation "Γ '⊢' t '∈' τ '|' ε" (at level 50).

Inductive has_type {W:world} {TV : Set} {V : Set} (Γ : @env W TV V): 
  expr W TV V -> typ W TV -> typ W TV -> Prop :=
| T_Req : forall (e : expr W TV V) (τ ε_1 ε_2:typ W TV),
    ε_1 ≅ ε_2 ->
    Γ ⊢ e ∈ τ | ε_1 ->
    Γ ⊢ e ∈ τ | ε_2

| T_Con : forall (x : V) (ε : typ W TV) (b : W.(w_base_t)) (v : W.(w_base_v) b),
    ε ::: k_eff_row ->
    Γ ⊢ v_const b v ∈ t_base b | ε
| T_Var : forall (x : V) (ε : typ W TV),
    ε ::: k_eff_row ->
    Γ ⊢ v_var x ∈ (Γ x) | ε

| T_Lam : forall (e : expr W TV (inc V)) (σ σ_1 ε ε' STH: typ W TV),
    σ   ::: k_type ->
    σ_1 ::: k_type ->
    ε   ::: k_eff_row ->
    ε'  ::: k_eff_row ->
    Γ,+ σ_1 ⊢ e ∈ σ | ε -> 
    Γ ⊢ v_lam σ_1 e STH ∈ σ_1 ==>[ε] σ | ε'

| T_App : forall (e_1 e_2 : expr W TV V) (σ σ_2 ε : typ W TV),
    σ   ::: k_type ->
    σ_2 ::: k_type ->
    ε   ::: k_eff_row ->
    Γ ⊢ e_1 ∈ σ_2 ==>[ε] σ | ε ->
    Γ ⊢ e_2 ∈ σ_2 | ε ->
    Γ ⊢ e_app e_1 e_2 ∈ σ | ε

| T_Let : forall (e_1 : expr W TV V) (e_2 : expr W TV (inc V)) (σ σ_2 ε : typ W TV),  
    σ   ::: k_type ->
    σ_2 ::: k_type ->
    ε   ::: k_eff_row ->
    Γ ⊢ e_1 ∈ σ | ε ->
    Γ,+ σ ⊢ e_2 ∈ σ_2 | ε ->
    Γ ⊢ e_let e_1 e_2 ∈ σ | ε


(* FILL IN HERE *)

where "Γ '⊢' t '∈' τ '|' ε" := (@has_type _ _ _ Γ t τ ε).

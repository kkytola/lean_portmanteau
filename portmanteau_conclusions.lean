/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import tactic 
import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.borel_space
import measure_theory.bochner_integration
import topology.metric_space.basic
import topology.instances.real
import topology.instances.ennreal
import order.liminf_limsup
import portmanteau_definitions
import portmanteau_integrals
import portmanteau_cont_imp_closed
import portmanteau_open_imp_cont
import portmanteau_open_closed_imp_borel
import portmanteau_borel_imp_closed_cond



noncomputable theory
open set 
open classical
open measure_theory
open measurable_space
open filter
open_locale topological_space



namespace portmanteau



section concluding_the_equivalence_of_portmanteau_conditions


/-- `tfae_weak_conv_seq'` :
    Equivalent conditions for the weak convergence of a sequence of Borel probability
    measures on a topological space, in terms of integrals of bounded continuous functions.
    The second of these is the "textbook definition".
    (Further equivalent conditions can be obtained if one assumes that the space is a
    complete separable metric space, or at least that it is a metric space, or at least
    that indicators of all closed sets have decreasing continuous bounded approximations.) -/
theorem tfae_weak_conv_seq' {α : Type*} [topological_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tfae  [ tendsto μseq at_top (𝓝 μ) ,
            ∀ (f : α → ℝ) , continuous f → bdd_Rval f →
              tendsto (λ n, (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)) f)) at_top (𝓝 (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ f)) ,
            ∀ (f : cont_bdd_ennval α) , 
              tendsto (λ n, integrate_cont_bdd_ennval (μseq(n)) f) at_top (𝓝 (integrate_cont_bdd_ennval μ f)) ] :=
begin
  have equiv₁ := @weak_conv_seq_iff α _ μseq μ ,
  have equiv₂ := @weak_conv_seq_iff' α _ μseq μ ,
  tfae_finish ,
end


theorem weak_conv_seq_iff_portmanteau_open' {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ portmanteau_open (λ n , (μseq(n)).val) μ.val :=
begin
  split ,
  { intros hdefcond ,
    have hcontcond := weak_conv_seq_iff_portmanteau_continuous_ennval.mp hdefcond,
    have has_approx := metric_space_has_cont_approx_of_closed α ,
    have hclcond := @portmanteau_continuous_imp_closed_cond α _ has_approx (λ n , (μseq(n)).val) (λ n , (μseq(n)).prop) μ.val μ.prop hcontcond ,
    exact (portmanteau_closed_and_open_cond_equivalent (λ n , (μseq(n)).val) (λ n , (μseq(n)).prop) μ.val μ.prop).mp hclcond , } ,
  { intros hopcond ,
    have textbook' := portmanteau_open_imp_cont (λ n , (μseq(n)).val) (λ n , (μseq(n)).prop) μ.val μ.prop hopcond ,
    apply weak_conv_seq_iff'.mpr ,
    intros f ,
    exact textbook' f.val f.prop.1 f.prop.2 , } ,
end


/-- `weak_conv_seq_iff_portmanteau_open'` :
    Equivalent characterization for the weak convergence of a sequence of Borel probability
    measures using open sets. -/
theorem weak_conv_seq_iff_portmanteau_open {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ ( ∀ (G : set α) , (is_open G) → μ(G) ≤ liminf at_top (λ n , (μseq(n))(G)) ) :=
begin
  split ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_open'.mp h , } ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_open'.mpr h , } ,
end


theorem weak_conv_seq_iff_portmanteau_closed' {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ portmanteau_closed (λ n , (μseq(n)).val) μ.val :=
begin
  have eq_open_closed := portmanteau_closed_and_open_cond_equivalent (λ n , (μseq(n)).val) (λ n , (μseq(n)).prop) μ.val μ.prop ,
  have eq_open_def := @weak_conv_seq_iff_portmanteau_open' _ _ μseq μ ,
  cc ,
end


/-- `weak_conv_seq_iff_portmanteau_closed'` :
    Equivalent characterization for the weak convergence of a sequence of Borel probability
    measures using closed sets. -/
theorem weak_conv_seq_iff_portmanteau_closed {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ ( ∀ (F : set α) , (is_closed F) → limsup at_top (λ n , (μseq(n))(F)) ≤ μ(F) ) :=
begin
  split ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_closed'.mp h , } ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_closed'.mpr h , } ,
end


theorem weak_conv_seq_iff_portmanteau_borel' {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ portmanteau_borel (λ n , (μseq(n)).val) μ.val :=
begin
  have closed_imp_borel := portmanteau_closed_imp_borel (λ n , (μseq(n)).val) (λ n , (μseq(n)).prop) μ.val μ.prop ,
  have borel_imp_closed := portmanteau_borel_imp_closed (λ n , (μseq(n)).val) (λ n , (μseq(n)).prop) μ.val μ.prop ,
  have eq_closed_def := @weak_conv_seq_iff_portmanteau_closed _ _ μseq μ ,
  split ,
  { intros hdefcond ,
    exact closed_imp_borel (eq_closed_def.mp hdefcond) , } ,
  { intros hborcond ,
    exact eq_closed_def.mpr (borel_imp_closed hborcond) , } ,
end


/-- `weak_conv_seq_iff_portmanteau_borel'` :
    Equivalent characterization for the weak convergence of a sequence of Borel probability
    measures using Borel sets whose frontiers (boundaries) carry no probability mass in the
    limit measure. -/
theorem weak_conv_seq_iff_portmanteau_borel {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ ( ∀ (E : set α) , (borel_set(α) E) → (μ(frontier E) = 0)
          → (tendsto (λ n , (μseq(n))(E)) at_top (𝓝 (μ(E))) ) ) :=
begin
  split ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_borel'.mp h , } ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_borel'.mpr h , } ,
end


/-- `tfae_weak_conv_seq` :
    Equivalent conditions for the weak convergence of a sequence of Borel probability
    measures on a metric space. -/
theorem tfae_weak_conv_seq {α : Type*} [metric_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tfae  [ tendsto μseq at_top (𝓝 μ) ,
            ∀ (f : α → ℝ) , continuous f → bdd_Rval f →
              tendsto (λ n, (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)) f)) at_top (𝓝 (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ f)) ,
            ∀ (f : cont_bdd_ennval α) , 
              tendsto (λ n, integrate_cont_bdd_ennval (μseq(n)) f) at_top (𝓝 (integrate_cont_bdd_ennval μ f)) ,
            ( ∀ (G : set α) , (is_open G) → μ(G) ≤ liminf at_top (λ n , (μseq(n))(G)) ) ,
            ( ∀ (F : set α) , (is_closed F) → limsup at_top (λ n , (μseq(n))(F)) ≤ μ(F) ) ,
            ( ∀ (E : set α) , (borel_set(α) E) → (μ(frontier E) = 0) → (tendsto (λ n , (μseq(n))(E)) at_top (𝓝 (μ(E))) ) ) ] :=
begin
  have equiv₁ := @weak_conv_seq_iff α _ μseq μ ,
  have equiv₂ := @weak_conv_seq_iff' α _ μseq μ ,
  have equiv₃ := @weak_conv_seq_iff_portmanteau_open α _ μseq μ ,
  have equiv₄ := @weak_conv_seq_iff_portmanteau_closed α _ μseq μ ,
  have equiv₅ := @weak_conv_seq_iff_portmanteau_borel α _ μseq μ ,
  tfae_finish ,
end



end concluding_the_equivalence_of_portmanteau_conditions


end portmanteau



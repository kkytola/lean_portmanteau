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
--import portmanteau_limsup_lemmas



noncomputable theory
open set 
open classical
open measure_theory
open measurable_space
open filter
open_locale topological_space



namespace portmanteau



abbreviation lim_R (s : ℕ → ℝ) (l : ℝ) : Prop := tendsto s at_top (𝓝 l)

abbreviation lim_enn (s : ℕ → ennreal) (l : ennreal) : Prop := tendsto s at_top (𝓝 l)

abbreviation bdd_Rval {β : Type*} (f : β → ℝ) : Prop :=
  ∃ (M : ℝ) , ∀ (b : β) , abs(f(b)) ≤ M

abbreviation bdd_ennval {α : Type*} (f : α → ennreal) : Prop :=
  ∃ (M : nnreal) , ∀ (a : α) , f(a) ≤ M


/-
lemma bdd_ennval_of_le_cst' {α : Type*} {f : α → ennreal} {c : nnreal} (h : f ≤ (λ a , c)) :
  bdd_ennval f := by { use c , exact h , }


lemma bdd_ennval_of_le_cst {α : Type*} {f : α → ennreal} {c : ennreal} (h : f ≤ (λ a , c)) (hc : c ≠ ⊤) :
  bdd_ennval f :=
begin
  use c.to_nnreal ,
  intros a , 
  have key := h a , 
  rwa ← ennreal.coe_to_nnreal hc at key ,
end
-/


lemma lim_R_rw (s : ℕ → ℝ) (l : ℝ) : lim_R s l = tendsto s at_top (𝓝 l) := by refl


section test_functions_for_weak_convergence


/-- Continuous bounded functions on a topological space `α` with values
in `ennreal` are used as "test functions" in the definition of the topology of
the weak convergence of probability measures. They are defined as a subtype
of `α → ennreal`, so that the type of (positive) functionals is just
`(cont_bdd_ennval α) → ennreal`. -/
def cont_bdd_ennval (α : Type*) [topological_space α] : Type*
  := { f : α → ennreal // continuous f ∧ bdd_ennval f }


def functional_cont_bdd_ennval (α : Type*) [topological_space α] : Type*
  := (cont_bdd_ennval α) → ennreal


instance {α : Type*} [topological_space α] :
  has_coe (cont_bdd_ennval α) (α → ennreal) := ⟨subtype.val⟩


@[simp] lemma val_eq_coe_testfun {α : Type*} [topological_space α] (f : cont_bdd_ennval α) :
  f.val = f := rfl


/-- As a first step towards the definition of the topology of the weak convergence
of probability measures, the space of functionals `(cont_bdd_ennval α) → ennreal`
is equipped with the product topology (the topology of "testfunctionwise" convergence,
i.e., of pointwise convergence of the functionals defined on the space of continuous
bounded test functions). -/
instance {α : Type*} [topological_space α] :
  topological_space (functional_cont_bdd_ennval α) := Pi.topological_space


/-- In an alternative an more familiar formulation, continuous bounded `ℝ`-valued
functions on a topological space `α` are used as "test functions" in the definition
of the topology of the weak convergence of probability measures. They are defined as
a subtype of `α → ℝ`. -/
def cont_bdd_Rval (α : Type*) [topological_space α] : Type*
  := { f : α → ℝ // continuous f ∧ bdd_Rval f }


def cont_bdd_Rval_mk {α : Type*} [topological_space α] 
  (g : α → ℝ) (g_cont : continuous g) (g_bdd : bdd_Rval g) : cont_bdd_Rval α :=
{ val := g ,
  property := ⟨ g_cont , g_bdd ⟩ , }

-- TODO: It would be good to equip `cont_bdd_Rval` with the sup-norm, show that it is
-- a Banach space, define the (continuous) dual of it, equip it with the dual norm,
-- show that each Borel probability measure defines an element of the (continuous)
-- dual, etc... At least currently the result `weak_conv_seq_iff` essentially shows
-- that the mapping the Borel probability measures into the dual will be an
-- embedding (the topologies are compatible).


--TODO: I can't use the same name for the following coercion.
--instance {α : Type*} [topological_space α] :
--  has_coe (cont_bdd_Rval α) (α → ℝ) := ⟨subtype.val⟩


end test_functions_for_weak_convergence



section topology_of_weak_convergence


/-- Borel probability measures on a topological space `α` are defined as a subtype
of measures. This subtype `borel_proba α` is equipped with the topology of weak
convergence. -/
def borel_proba (α : Type*) [topological_space α] : Type
  := { μ : @measure_theory.measure α (borel(α)) // @probability_measure α (borel(α)) μ }


instance (α : Type*) [topological_space α] :
  has_coe (borel_proba α) (@measure_theory.measure α (borel(α))) := ⟨subtype.val⟩


@[simp] lemma val_eq_coe_borel_proba {α : Type*} [topological_space α] (ν : borel_proba α) :
  ν.val = ν := rfl


abbreviation integrate_cont_bdd_ennval {α : Type*} [topological_space α]
  (μ : borel_proba α) (f : cont_bdd_ennval α) : ennreal := @lintegral α (borel(α)) μ f 


/-- The topology of weak convergence on `borel_proba α` is defined as the induced
topology of the mapping `(borel_proba α) → ((cont_bdd_ennval α) → ennreal)` to
functionals defined by integration of a test functio against to the measure. In
other contexts this could be called the weak-* topology. -/
instance {α : Type} [topological_space α] : topological_space (borel_proba α)
  := topological_space.induced (λ (μ : borel_proba α) , integrate_cont_bdd_ennval μ) infer_instance


/-- Integration of test functions against borel probability measures depends
continuously on the measure. -/
lemma integrate_cont_bdd_ennval_cont {α : Type} [topological_space α] :
  continuous (@integrate_cont_bdd_ennval α _) := continuous_induced_dom


-- Remark: It felt convenient to isolate the following fact (does it exist already?).
lemma conv_seq_induced {α γ : Type*} [top_γ : topological_space γ]
  (f : α → γ) (x : ℕ → α) (x₀ : α) :
    tendsto (f ∘ x) at_top (𝓝 (f(x₀)))
      → tendsto x at_top (@nhds α (topological_space.induced f top_γ) x₀) :=
begin
  intro h_f_lim ,
  apply tendsto_nhds.mpr ,
  intros U open_U U_ni_x₀ ,
  rcases ((@is_open_induced_iff α γ top_γ U f).mp open_U) with ⟨ V , open_V , preim_V_eq_U ⟩ ,
  induction preim_V_eq_U , 
  apply tendsto_nhds.mp h_f_lim V open_V U_ni_x₀ , 
end


/-- The usual definition of weak convergence of probability measures is given in
terms of sequences of probability measures: it is the requirement that the integrals
of all continuous bounded functions against members of the sequence converge.
This characterization is shown in `weak_conv_seq_iff'` in the case when the
functions are `ennreal`-valued and the integral is `lintegral`. The most common
formulation with `ℝ`-valued functions and Bochner integrals is `weak_conv_seq_iff`. -/
theorem weak_conv_seq_iff' {α : Type*} [topological_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ ∀ (f : cont_bdd_ennval α) , 
        tendsto (λ n, integrate_cont_bdd_ennval (μseq(n)) f) at_top (𝓝 (integrate_cont_bdd_ennval μ f)) :=
begin
  split ,
  { intros weak_conv ,
    have key := tendsto.comp (continuous.tendsto (@integrate_cont_bdd_ennval_cont α _) μ) weak_conv ,
    exact tendsto_pi.mp key , } ,
  { intro h_lim_forall ,
    have h_lim : tendsto (λ n, integrate_cont_bdd_ennval (μseq(n))) at_top (𝓝 (integrate_cont_bdd_ennval μ)) ,
    { exact tendsto_pi.mpr h_lim_forall , } ,
    exact conv_seq_induced _ μseq μ h_lim , } ,
end



section equivalent_conditions
-- See <pormanteau_conclusions.lean> for the main theorems about the equivalence.


abbreviation portmanteau_continuous_ennval {α : Type} [topological_space α]
  (μseq : ℕ → @measure_theory.measure α (borel α)) (μ : @measure_theory.measure α (borel α)) : Prop :=
    ∀ (f : α → ennreal) , (continuous f) → (bdd_ennval f) →
      lim_enn (λ n , (@lintegral α (borel(α)) (μseq(n)) f) ) (@lintegral α (borel(α)) μ f)


abbreviation portmanteau_continuous_Rval {α : Type} [topological_space α]
  (μseq : ℕ → @measure_theory.measure α (borel α)) (μ : @measure_theory.measure α (borel α)) : Prop :=
    ∀ (f : α → ℝ) , (continuous f) → (bdd_Rval f) →
      lim_R (λ n , (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)) f)) (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ f)


abbreviation portmanteau_open {α : Type} [topological_space α]
  (μseq : ℕ → @measure_theory.measure α (borel α)) (μ : @measure_theory.measure α (borel α)) : Prop :=
    ∀ (G : set α) , (is_open G) → μ(G) ≤ liminf at_top (λ n , (μseq(n))(G))


abbreviation portmanteau_closed {α : Type} [topological_space α]
  (μseq : ℕ → @measure_theory.measure α (borel α)) (μ : @measure_theory.measure α (borel α)) : Prop :=
    ∀ (F : set α) , (is_closed F) → limsup at_top (λ n , (μseq(n))(F)) ≤ μ(F)


abbreviation portmanteau_borel {α : Type} [topological_space α]
  (μseq : ℕ → @measure_theory.measure α (borel α)) (μ : @measure_theory.measure α (borel α)) : Prop :=
    ∀ (E : set α) , ((borel α).measurable_set' E) → (μ(frontier E) = 0)
      → (lim_enn (λ n , (μseq(n))(E)) (μ(E)))


end equivalent_conditions


end topology_of_weak_convergence




























/-

section portmanteau_definitions




notation `borel_measure`(α) := @measure_theory.measure α (borel α)
notation `borel_set`(α) E := (borel α).measurable_set' E


/-
def bdd_ennrealval' {β : Type*} (f : β → ennreal) : Prop :=
  ∃ (M : nnreal) , ∀ (b : β) , f(b) ≤ M

def bdd_Rval' {β : Type*} (f : β → ℝ) : Prop :=
  ∃ (M : ℝ) , ∀ (b : β) , abs(f(b)) ≤ M
-/

--abbreviation ulbdd_Rval {β : Type*} (f : β → ℝ) : Prop :=
--  ∃ (L U : ℝ) , ∀ (b : β) , L ≤ f(b) ∧ f(b) ≤ U

/-
def ulbdd_Rval' {β : Type*} (f : β → ℝ) : Prop :=
  ∃ (L U : ℝ) , ∀ (b : β) , L ≤ f(b) ∧ f(b) ≤ U
-/

--lemma bdd_iff_Rval {β : Type*} (f : β → ℝ) :
--  bdd_Rval f ↔ ulbdd_Rval f := sorry

--notation `∫` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := (@lintegral α (borel(α)) μ r)
--notation `∫⁻` binders `, ` r:(scoped:60 f, lintegral volume f) := r
--notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 :=
--  lintegral (measure.restrict μ s) r
--notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, lintegral (measure.restrict volume s) f) := r


notation `integrate` f ` ∂` μ := lintegral μ f --(@lintegral α (borel(α)) μ f)

variables {α : Type*} [topological_space α]

abbreviation enn_integrate (f : α → ennreal) (μ : borel_measure(α)) :=
  (@lintegral α (borel(α)) μ f)

/-
def enn_integrate (f : α → ennreal) (μ : borel_measure(α)) :=
  (@lintegral α (borel(α)) μ f)
-/

--variables (ν : borel_measure(α)) (f : α → ennreal)
--#check ( enn_integrate f ν )
--#check (@lintegral α (borel(α)) ν f)
--#check ( integrate f ∂ν )
--#check ( integrate f ∂ν )


abbreviation portmanteau_continuous_cond (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (f : α → ennreal) , (continuous f) → (bdd_ennrealval f) →
    lim_enn (λ n , (enn_integrate f (μseq(n))) ) (enn_integrate f μ) 

abbreviation portmanteau_continuous_cond_Rval (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (f : α → ℝ) , (continuous f) → (bdd_Rval f) →
    lim_R (λ n , (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)) f)) (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ f)

abbreviation portmanteau_open_cond (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (G : set α) , (is_open G) → μ(G) ≤ liminf_enn (λ n , (μseq(n))(G))

abbreviation portmanteau_closed_cond (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (F : set α) , (is_closed F) → limsup_enn (λ n , (μseq(n))(F)) ≤ μ(F)

abbreviation portmanteau_borel_cond (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (E : set α) , (borel_set(α) E) → (μ(frontier E) = 0)
    → (lim_enn (λ n , (μseq(n))(E)) (μ(E)))

def portmanteau_continuous_cond' (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (f : α → ennreal) , (continuous f) → (bdd_ennrealval f) →
    lim_enn (λ n , (enn_integrate f (μseq(n))) ) (enn_integrate f μ) 

def portmanteau_open_cond' (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (G : set α) , (is_open G) → μ(G) ≤ liminf_enn (λ n , (μseq(n))(G))

def portmanteau_closed_cond' (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (F : set α) , (is_closed F) → limsup_enn (λ n , (μseq(n))(F)) ≤ μ(F)

def portmanteau_borel_cond' (μseq : ℕ → (borel_measure(α))) (μ : borel_measure(α)) : Prop :=
  ∀ (E : set α) , (borel_set(α) E) → (μ(frontier E) = 0)
    → (lim_enn (λ n , (μseq(n))(E)) (μ(E)))



end portmanteau_definitions

-/


end portmanteau



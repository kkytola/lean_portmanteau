/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import tactic 
import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.borel_space
import topology.metric_space.basic
import topology.instances.real
import topology.instances.ennreal
import order.liminf_limsup
import portmanteau_limsup_lemmas
import portmanteau_definitions
import portmanteau_proba_lemmas
import analysis.seminorm


noncomputable theory
open set 
open classical
open measure_theory
open measurable_space
open metric_space
open borel_space
open filter
open order
open_locale topological_space ennreal big_operators


namespace portmanteau

section portmanteau_integrals


variables {α : Type} [topological_space α]

abbreviation R_integrate (f : α → ℝ) (μ : borel_proba α) := @integral α ℝ (borel(α)) _ _ _ _ _ _ μ f
abbreviation R_abs_nn : ℝ → nnreal := λ x , nnnorm x
abbreviation R_abs_enn : ℝ → ennreal := λ x , ennreal.of_nnreal_hom (nnnorm x) --ennreal.of_real(abs(x))


lemma R_abs_enn_le_of_abs_le {x c : ℝ} (h : abs(x) ≤ c) : R_abs_enn(x) ≤ ennreal.of_real(c) :=
begin
  have c_nn : 0 ≤ c := le_trans (abs_nonneg x) h,
  have eq := real.coe_to_nnreal c c_nn ,
  set c' := c.to_nnreal with hc' ,
  have h₁ : R_abs_nn(x) ≤ c' := (real.le_to_nnreal_iff_coe_le c_nn).mpr h ,
  exact (with_top.le_coe rfl).mpr h₁ ,
end


-- TODO: Should state for finite measures? 
lemma integrable_of_bdd_realval {β : Type*} {mβ : measurable_space β}
  (μ : measure β) [μ_fin : probability_measure μ]
  (f : β → ℝ) (f_bdd : bdd_Rval f) (f_mble : @ae_measurable β ℝ mβ _ f μ) :
     integrable f μ :=
begin
  cases f_bdd with c hc ,
  set f' := R_abs_enn ∘ f with hf' ,
  suffices : lintegral μ f' < ⊤ ,
  { rw hf' at this ,
    exact ⟨ f_mble , this ⟩ , } ,
  have bdd' : f' ≤ (λ b , ennreal.of_real(c)) ,
  { rw hf' ,
    intros b ,
    dsimp ,
    specialize hc b ,
    exact R_abs_enn_le_of_abs_le hc , } ,
  have integr_bdd := lintegral_mono bdd' ,
  set c' := ennreal.of_real(c) with hc' ,
  have const_integr : lintegral μ (λ b , c') = c' * (μ(univ)) ,
  { rw ← set_lintegral_const univ c' ,
    simp , } ,
  have total : c' * (μ(univ)) < ⊤ ,
  { rw (proba_muniv μ) ,
    simp , } ,
  rw ← const_integr at total ,
  exact lt_of_le_of_lt integr_bdd total , 
end


-- TODO: Should state for finite measures? 
lemma bdd_integral_of_bdd_ennval {β : Type*} {mβ : measurable_space β}
  (μ : measure β) [μ_fin : probability_measure μ]
  (f : β → ennreal) (f_bdd : bdd_ennval f) :
     lintegral μ f < ⊤ :=
begin
  cases f_bdd with c hc ,
  have f_le_c : f ≤ λ x , c := hc ,
  have integr_f_le := @lintegral_mono β mβ μ _ _ f_le_c ,
  simp [proba_muniv] at integr_f_le ,
  exact lt_of_le_of_lt integr_f_le (@ennreal.coe_lt_top c) ,
end


lemma const_bdd_Rval {β : Type*} {c : ℝ} :
    bdd_Rval (λ (x : β) , c) :=
begin
  use abs(c) ,
  intros x ,
  refl ,
end


lemma const_bdd_ennval {β : Type*} {c : nnreal} :
    bdd_ennval (λ (x : β) , c) :=
begin
  use c ,
  intros x ,
  simp only [ennreal.coe_le_coe] ,
end


-- TODO: Should state for finite measures?
lemma const_integrable {β : Type*} {mβ : measurable_space β}
  (μ : measure β) (μ_fin : probability_measure μ) (c : ℝ) :
    integrable (λ (x : β) , c) μ :=
begin
  apply integrable_const_iff.mpr ,
  right ,
  exact proba_finite μ univ ,
end


lemma integral_cst {β : Type*} {mβ : measurable_space β}
  (μ : measure β) (μ_fin : probability_measure μ) (c : ℝ) :
    integral μ (λ (x : β) , c) = c :=
begin
  suffices : integral μ (λ (x : β) , c) = (μ(univ)).to_real * c,
  { simp [proba_muniv μ] , } ,
  apply integral_const c ,
end

lemma lintegral_cst {β : Type*} {mβ : measurable_space β}
  (μ : measure β) [μ_proba : probability_measure μ] (c : ennreal) :
    lintegral μ (λ (x : β) , c) = c :=
begin
  suffices : lintegral μ (λ (x : β) , c) = c * (μ(univ)) ,
  { simp [proba_muniv μ] , } ,
  apply lintegral_const c ,
end


lemma integral_add_cst {β : Type*} {mβ : measurable_space β} {c : ℝ}
  (μ : measure β) [μ_fin : probability_measure μ] (f : β → ℝ) (f_intble: integrable f μ) :
    integral μ ( f + (λ (x : β) , c)) = integral μ f + c :=
begin
  have key := @integral_add β ℝ mβ _ _ _ _ _ _ f (λ (x : β) , c) μ f_intble (const_integrable μ μ_fin c) ,
  rw integral_cst μ μ_fin c at key ,
  exact key ,
end


lemma lintegral_cst_sub {β : Type*} {mβ : measurable_space β} {c : ennreal} 
  (μ : measure β) [μ_fin : probability_measure μ] (c_ne_top : c ≠ ⊤)
  (f : β → ennreal) (f_mble: measurable f) (f_le_c : f ≤ λ b , c) :
    lintegral μ ( (λ (x : β) , c) - f) = c - lintegral μ f :=
begin
  nth_rewrite 0 ←(lintegral_cst μ c) ,
  have f_intble := bdd_integral_of_bdd_ennval μ f (bdd_ennval_of_le_cst f_le_c c_ne_top) ,
  rw ← @lintegral_sub β mβ μ (λ (b : β) , c) f (measurable_const) f_mble f_intble (eventually_of_forall f_le_c) ,
  refl ,
end


lemma nnreal_integral_of_integrable_nonneg {β : Type*} {mβ : measurable_space β}
  (μ : measure β) (f : β → ℝ) (f_nn : 0 ≤ f) 
  (f_intble : integrable f μ) :
     ennreal.of_real (integral μ f) = lintegral μ (ennreal.of_real ∘ f) :=
begin
  set g := λ (b : β) , (f(b)).to_nnreal with hg ,
  have key := @lintegral_coe_eq_integral β mβ μ g (integrable.max_zero f_intble) ,
  rw hg at key ,
  set ψ : (β → nnreal) → (β → ℝ) := coe with hψ ,
  have eq₀ : f = ψ(g) ,
  { funext b ,
    exact left_eq_sup.mpr (f_nn b) , } , 
  have eq₂ : ∫ (a : β), ↑((λ (b : β), (f b).to_nnreal) a) ∂μ = integral μ (ψ(g)) := by refl ,
  rw [eq₂ , ←eq₀] at key ,
  rw ← key ,
  refl ,
end


lemma nnreal_integral_of_integrable_nonneg' {β : Type*} {mβ : measurable_space β}
  (μ : measure β) (f : β → ℝ) (f_nn : 0 ≤ f) 
  (f_intble : integrable f μ) :
     integral μ f = (lintegral μ (ennreal.of_real ∘ f)).to_real :=
begin
  have key := nnreal_integral_of_integrable_nonneg μ f f_nn f_intble ,
  have fin : lintegral μ (ennreal.of_real ∘ f) ≠ ⊤ ,  
  { rw ←key ,
    exact ennreal.of_real_ne_top , } ,
  have nn : 0 ≤ integral μ f := integral_nonneg f_nn ,
  have eq := ennreal.to_real_of_real nn ,
  rw key at eq ,
  exact eq.symm ,
end


example (s : ℕ → ℝ) (l : ℝ) (hlim : tendsto s at_top (𝓝 l)) (c : ℝ) :
  tendsto (λ (n : ℕ) , s(n) + c) at_top (𝓝 (l+c)) :=
begin
  exact tendsto.add_const c hlim ,
end


lemma nonneg_of_add_abs_le (a c : ℝ) (h : abs(a) ≤ c) : 0 ≤ c + a :=
begin
  have key : c-abs(a) ≤ c+a := by linarith [neg_le.mp (neg_le_abs_self a)] ,
  exact le_trans (sub_nonneg.mpr h) key ,
end


private lemma portmanteau_continuous_equivalent_formulation'
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    portmanteau_continuous_ennval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ 
      → portmanteau_continuous_Rval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ :=
begin
  intros cc_ennrealval ,
  intros g g_cont g_bdd ,
  have g_bdd' := g_bdd ,
  cases g_bdd' with c hc ,
  set h := (g + (λ x, c)) with hh ,
  set f := λ (x : α) , ennreal.of_real (h(x)) with hf ,
  have h_nn : 0 ≤ h ,
  { intros x ,
    rw hh ,
    have samediff := nonneg_of_add_abs_le (g(x)) c (hc x) ,
    rwa add_comm at samediff , } ,
  have f_eq_h : f = ennreal.of_real ∘ h := by refl ,
  have h_bdd : bdd_Rval h := bdd_Rval_add g_bdd const_bdd_Rval ,
  have h_cont : continuous h := continuous.add g_cont (@continuous_const α ℝ _ _ c ) ,
  have f_bdd : bdd_ennval f := bdd_ennval_of_bdd_Rval h_bdd ,
  have f_cont : continuous f := cont_enn_of_cont_R h h_cont , 
  specialize cc_ennrealval f f_cont f_bdd ,
  have g_mble := continuous.borel_measurable g_cont ,
  have h_mble := continuous.borel_measurable h_cont ,
  have g_ae_mble := @measurable.ae_measurable α ℝ (borel(α)) _ g μ g_mble ,
  have h_ae_mble := @measurable.ae_measurable α ℝ (borel(α)) _ h μ h_mble ,
  have g_ae_mble_seq := λ n , @measurable.ae_measurable α ℝ (borel(α)) _ g (μseq(n)) g_mble ,
  have h_ae_mble_seq := λ n , @measurable.ae_measurable α ℝ (borel(α)) _ h (μseq(n)) h_mble ,
  have g_intble := @integrable_of_bdd_realval _ _ μ.val μ.prop g g_bdd g_ae_mble ,
  have h_intble := @integrable_of_bdd_realval _ _ μ.val μ.prop h h_bdd h_ae_mble ,
  have g_intble_seq := λ n , @integrable_of_bdd_realval _ _ (μseq(n)).val (μseq(n)).prop g g_bdd (g_ae_mble_seq n) ,
  have h_intble_seq := λ n , @integrable_of_bdd_realval _ _ (μseq(n)).val (μseq(n)).prop h h_bdd (h_ae_mble_seq n) ,
  suffices : lim_R (λ n , (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)) h)) (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ h) ,
  { have add_cst : (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ h) = (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ g) + c ,
    { rw hh ,
      apply @integral_add_cst _ _ _ μ.val μ.prop g g_intble , } ,
    have add_cst_seq : (λ n , (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq n) h)) = (λ n , (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq n) g) + c) ,
    { funext n ,
      rw hh ,
      apply @integral_add_cst _ _ _ (μseq(n)).val (μseq(n)).prop g (g_intble_seq n) , } ,
    rw [add_cst , add_cst_seq] at this ,
    have shift_lim := tendsto.add_const (-c) this ,
    simp at shift_lim ,
    exact shift_lim , } , 
  have eq := nnreal_integral_of_integrable_nonneg' μ.val h h_nn h_intble ,
  have eq_seq := λ n , nnreal_integral_of_integrable_nonneg' (μseq(n)).val h h_nn (h_intble_seq n) ,
  have eq' : @integral α ℝ (borel(α)) _ _ _ _ _ _ μ h = (@lintegral α (borel(α)) μ f).to_real := eq ,
  have eq_seq' : (λ n , @integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)).val h) = ennreal.to_real ∘ (λ n , (@lintegral α (borel(α)) (μseq(n)) f)) ,
  { funext n ,
    exact eq_seq n , } ,
  have fin : @lintegral α (borel(α)) μ f ≠ ⊤
    := ne_of_lt (@bdd_integral_of_bdd_ennval α (borel(α)) μ μ.prop f f_bdd) , 
  have key := lim_R_of_lim_enn _ _ cc_ennrealval fin ,
  rw ←eq' at key ,
  rw ←eq_seq' at key ,
  exact key , 
end


private lemma portmanteau_continuous_equivalent_formulation''
  {μseq : ℕ → (borel_proba α)} {μ : borel_proba α} :
    portmanteau_continuous_Rval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ
       → portmanteau_continuous_ennval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ :=
begin
  intros cc_Rval ,
  intros f f_cont f_bdd ,
  have f_fin_val : ∀ (x : α) , f(x) ≠ ⊤ := finval_of_bdd_ennval f_bdd ,
  set g := λ (x : α) , ennreal.to_real (f(x)) with hg ,
  have f_eq_g : f = ennreal.of_real ∘ g ,
  { funext x ,
    exact (ennreal.of_real_to_real (f_fin_val x)).symm , } , 
  have g_nn : 0 ≤ g ,
  { intros x ,
    simp only [pi.zero_apply, ennreal.to_real_nonneg] , } ,
  have g_bdd : bdd_Rval g ,
  { cases f_bdd with c hc ,
    use c ,
    intros x ,
    rw hg ,
    specialize hc x ,
    have abs_eq : (abs (f(x)).to_real) = g(x) := by simp only [ennreal.to_real_nonneg, abs_eq_self] ,
    rw hg at abs_eq ,
    dsimp at * ,
    rw abs_eq ,
    exact ennreal.to_real_le_coe_of_le_coe hc , } ,
  have g_cont : continuous g := cont_R_of_cont_bdd_enn f f_cont f_bdd , 
  have g_mble := continuous.borel_measurable g_cont ,
  have g_ae_mble := @measurable.ae_measurable α ℝ (borel(α)) _ g μ g_mble ,
  have g_ae_mble_seq := λ n , @measurable.ae_measurable α ℝ (borel(α)) _ g (μseq(n)) g_mble ,
  have g_intble := @integrable_of_bdd_realval _ _ μ.val μ.prop g g_bdd g_ae_mble ,
  have g_intble_seq := λ n , @integrable_of_bdd_realval _ _ (μseq(n)).val (μseq(n)).prop g g_bdd (g_ae_mble_seq n) ,
  have eq := nnreal_integral_of_integrable_nonneg μ.val g g_nn g_intble ,
  have eq_seq := λ n , nnreal_integral_of_integrable_nonneg (μseq(n)).val g g_nn (g_intble_seq n) ,
  rw ← f_eq_g at * ,
  have eq' : ennreal.of_real (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ g) = @lintegral α (borel(α)) μ f := eq ,
  have eq_seq' : (λ n , ennreal.of_real (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq n) g)) = (λ n , @lintegral α (borel(α)) (μseq n) f) , -- := by simp [eq_seq] ,
  { funext n ,
    exact eq_seq n , } ,
  rw ←eq' ,
  rw ←eq_seq' ,
  specialize cc_Rval g g_cont g_bdd ,
  exact lim_enn_of_lim_R cc_Rval , 
end


/-- The usual definition of weak convergence of probability measures is given in
terms of sequences of probability measures: it is the requirement that the integrals
of all continuous bounded functions against members of the sequence converge.
This characterization is shown in `weak_conv_seq_iff`. -/
theorem weak_conv_seq_iff {α : Type*} [topological_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ ( ∀ (f : α → ℝ) , continuous f → bdd_Rval f →
          tendsto (λ n, (@integral α ℝ (borel(α)) _ _ _ _ _ _ (μseq(n)) f)) at_top (𝓝 (@integral α ℝ (borel(α)) _ _ _ _ _ _ μ f)) ) :=
begin
  split ,
  { intros weak_conv ,
    have key := weak_conv_seq_iff'.mp weak_conv ,
    have key' : portmanteau_continuous_ennval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ ,
    { intros f f_cont f_bdd ,
      exact key ⟨ f , ⟨ f_cont , f_bdd ⟩ ⟩ , } ,
    exact portmanteau_continuous_equivalent_formulation' key' , } , 
  { intros h ,
    have key := portmanteau_continuous_equivalent_formulation'' h ,
    apply weak_conv_seq_iff'.mpr ,
    intros f ,
    exact key f.val f.prop.1 f.prop.2 , } , 
end


theorem weak_conv_seq_iff_portmanteau_continuous_Rval {α : Type*} [topological_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ portmanteau_continuous_Rval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ 
        := weak_conv_seq_iff 


theorem weak_conv_seq_iff_portmanteau_continuous_ennval {α : Type*} [topological_space α]
  {μseq : ℕ → borel_proba α} {μ : borel_proba α} :
    tendsto μseq at_top (𝓝 μ) 
      ↔ portmanteau_continuous_ennval (λ n , (μseq(n) : @measure_theory.measure α (borel(α)))) μ :=
begin
  split ,
  { intros h ,
    exact portmanteau_continuous_equivalent_formulation'' (weak_conv_seq_iff_portmanteau_continuous_Rval.mp h) , } ,
  { intros h ,
    exact weak_conv_seq_iff_portmanteau_continuous_Rval.mpr (portmanteau_continuous_equivalent_formulation' h) , } ,
end



end portmanteau_integrals

end portmanteau



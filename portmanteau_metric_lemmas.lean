/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import tactic 
import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.borel_space
import measure_theory.lebesgue_measure
import topology.metric_space.basic
import topology.instances.real
import topology.instances.ennreal
import order.liminf_limsup
import portmanteau_limsup_lemmas
import portmanteau_topological_lemmas
import portmanteau_proba_lemmas



noncomputable theory
open set 
open classical
open measure_theory
open measurable_space
open metric_space
open metric
open real
open borel_space
open filter
open order
open tactic.interactive
open_locale topological_space ennreal big_operators classical


namespace portmanteau



section portmanteau_metric_lemmas


variables {α : Type*} [metric_space α]
variables (G E F : set α)


/- ## Distance to a set, thickening, etc.
-/


abbreviation thickening_o (δ : ℝ) (E : set α) : set α :=
    {x : α | ((inf_dist x E) < δ) }


abbreviation thickening_c (δ : ℝ) (E : set α) : set α :=
    {x : α | ((inf_dist x E) ≤ δ) }


lemma thickening_o_def {δ : ℝ} {E : set α} :
  thickening_o δ E = {x : α | ((inf_dist x E) < δ) } := by refl


lemma thickening_c_def {δ : ℝ} {E : set α} :
  thickening_c δ E = {x : α | ((inf_dist x E) ≤ δ) } := by refl


lemma thickening_o_preimage {δ : ℝ} {E : set α} : 
  thickening_o δ E = (λ (x : α) , (inf_dist x E))⁻¹' {u : ℝ | u < δ} := by refl 


lemma thickening_c_preimage {δ : ℝ} {E : set α} : 
  thickening_c δ E = (λ (x : α) , (inf_dist x E))⁻¹' {u : ℝ | u ≤ δ} := by refl 


lemma thickening_o_subset_thickening_c (δ : ℝ) (E : set α) :
  thickening_o δ E ⊆ thickening_c δ E :=
begin
  intros x hx ,
  simp only [mem_set_of_eq] at * ,
  linarith ,
end


lemma thickening_c_subset_thickening_o {δ₁ δ₂ : ℝ} (h_lt : δ₁ < δ₂) (E : set α) :
  thickening_c δ₁ E ⊆ thickening_o δ₂ E :=
begin
  intros x hx ,
  simp only [mem_set_of_eq] at * ,
  linarith ,
end


lemma thickening_o_subset_thickening_o {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : set α) :
  thickening_o δ₁ E ⊆ thickening_o δ₂ E :=
begin
  intros x hx ,
  simp only [mem_set_of_eq] at * ,
  linarith ,
end


lemma thickening_c_subset_thickening_c {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : set α) :
  thickening_c δ₁ E ⊆ thickening_c δ₂ E :=
begin
  intros x hx ,
  simp only [mem_set_of_eq] at * ,
  linarith ,
end


lemma is_open_thickening_o {δ : ℝ} {E : set α} :
  is_open (thickening_o δ E) :=
begin
  have cont_dist := continuous_inf_dist_pt E ,
  have ival_open : is_open {u : ℝ | u < δ} := is_open_gt' _ ,
  have open_pre := continuous.is_open_preimage cont_dist {u : ℝ | u < δ} ival_open ,
  assumption ,
end


lemma is_closed_thickening_c {δ : ℝ} {E : set α} :
    is_closed (thickening_c δ E) :=
begin
  have cont_dist := continuous_inf_dist_pt E ,
  have ival_closed : is_closed {u : ℝ | u ≤ δ} := is_closed_le' _ ,
  have closed_pre := continuous_iff_is_closed.mp cont_dist {u : ℝ | u ≤ δ} ival_closed ,
  assumption ,
end


lemma closure_inter_thickening_c (E : set α) [non_emp : E.nonempty] :
  closure E = ⋂ δ ∈ {δ' : ℝ | 0 < δ'} , thickening_c δ E :=
begin
  have inter_zero_dist : ∀ (z : α) ,
      z ∈ ( ⋂ (δ > 0) , (thickening_c δ E)) ↔ (inf_dist z E = 0) ,
  { intros z ,
    split ; intro hz ,
    { simp only [gt_iff_lt, mem_Inter, mem_set_of_eq] at hz ,
      set r := inf_dist z E with hr ,
      have r_nn : 0 ≤ r := inf_dist_nonneg ,
      have r_np := le_of_forall_le_of_dense hz ,
      linarith , } ,
    { simp only [gt_iff_lt, mem_Inter, mem_set_of_eq] ,
      intros ε hε ,
      rw hz ,
      linarith , } ,
    } ,
  have closure_zero_dist : ∀ (z : α) ,
      z ∈ closure E ↔ (inf_dist z E = 0) ,
  { intros z ,
    apply mem_closure_iff_inf_dist_zero ,
    exact non_emp , } ,
  ext x ,
  exact iff.trans (closure_zero_dist x) (inter_zero_dist x).symm ,
end


example (E : set α) (nemp : E.nonempty) : E ≠ ∅ :=
begin
  exact nonempty.ne_empty nemp,
end


lemma closure_subset_thickening_c (δ : ℝ) (δ_pos : 0 < δ) (E : set α) : 
  closure E ⊆ thickening_c δ E :=
begin
  by_cases E = ∅ ,
  { simp only [h, empty_subset, closure_empty] , } , 
  { have nonemp : E.nonempty := ne_empty_iff_nonempty.mp h,
    have key := @closure_inter_thickening_c _ _ E nonemp ,
    rw [key , subset_def ] ,
    tidy , } , 
end


lemma closure_subset_thickening_o (δ : ℝ) (δ_pos : 0 < δ) (E : set α) : 
  closure E ⊆ thickening_o δ E :=
begin
  by_cases E = ∅ ,
  { simp only [h, empty_subset, closure_empty] , } , 
  { have key := closure_subset_thickening_c (δ/2) (by linarith) E ,
    have plot := @thickening_c_subset_thickening_o _ _ (δ/2) δ (by linarith) E ,
    exact subset.trans key plot , } , 
end


lemma closure_inter_thickening_o (E : set α) (non_emp : E.nonempty) :
  closure E = ⋂ δ ∈ {δ' : ℝ | 0 < δ'} , thickening_o δ E :=
begin
  apply subset.antisymm ,
  { have key : ∀ (δ : ℝ) , (0 < δ) → (closure E ⊆ thickening_o δ E) ,
    { intros δ hδ ,
      exact closure_subset_thickening_o δ hδ E, } ,
    exact subset_bInter key , } , 
  { rw @closure_inter_thickening_c _ _ E non_emp ,
    refine bInter_mono _ ,
    intros δ δ_pos' ,
    exact thickening_o_subset_thickening_c δ E , } , 
end


lemma closure_inter_seq_thickening_o (E : set α) (non_emp : E.nonempty)
  (δseq : ℕ → ℝ) (h_pos : ∀ n , 0 < δseq(n)) (hlim : lim_R δseq 0) :
  closure E = ⋂ n : ℕ , thickening_o (δseq(n)) E :=
begin
  apply subset.antisymm ,
  { have key' := (λ n , closure_subset_thickening_o (δseq(n)) (h_pos n) E ) ,
    exact subset_Inter key' , } , 
  { intros x hx ,
    rw closure_inter_thickening_o E non_emp ,
    rw mem_Inter at hx ,
    rw mem_Inter ,
    rintros ε T hTε , 
    simp only [exists_prop, mem_range, mem_set_of_eq] at hTε ,
    cases hTε with εpos hT ,
    have small : ( ∃ n , ∀ k , n ≤ k → δseq(k) ≤ ε ) ,
    { specialize hlim (Iic_mem_nhds εpos) ,
      tidy , } ,
    cases small with n hn ,
    specialize hn n (rfl.ge) ,
    specialize hx n ,
    rw ← hT ,
    apply thickening_o_subset_thickening_o hn E ,
    exact hx , } , 
end


def approx_indicator_seq_thickening_o (E : set α) (non_emp : E.nonempty)
  (δseq : ℕ → ℝ) (hpos : ∀ n , 0 < δseq(n)) 
  (hdecr : is_decreasing_seq δseq) (hlim : lim_R δseq 0) :
    ptwise_decr_mble_lim_ennreal (borel(α)) (indic (closure E)) :=
{
  funseq := (λ n , (indic (thickening_o (δseq(n)) E))) ,
  decr := begin
    intros n m hnm ,
    have plot := thickening_o_subset_thickening_o (hdecr hnm) E ,
    exact indic_mono _ _ plot ,
  end ,
  limit := begin
    have key := closure_inter_seq_thickening_o E non_emp δseq hpos hlim ,
    intros x ,
    by_cases x ∈ closure E ,
    { have hall : (λ n , (indic (thickening_o (δseq(n)) E) x)) = (λ n , 1) ,
      { funext n ,
        rw key at h ,
        rw mem_Inter at h ,
        exact (indic_val_one_iff _ x).mpr (h n) , } ,
      rw [ hall , ((indic_val_one_iff _ x).mpr h) ] ,
      exact tendsto_const_nhds , } , 
    { rw (indic_val_zero_iff _ x).mpr h ,
      have zero : (lim_enn (λ n , 0) 0) := tendsto_const_nhds ,
      apply lim_enn_of_ev_same (λ n , 0) _ _ zero , 
      rw key at h ,
      simp only [mem_Inter, not_lt, ge_iff_le, mem_set_of_eq, not_forall] at h,
      cases h with m hm ,
      use m ,
      intros k hk ,
      rw (indic_val_zero_iff _ x).mpr ,
      have plot := thickening_o_subset_thickening_o (hdecr hk) E ,
      rw thickening_o_def at * ,
      simp only [set_of_subset_set_of, not_lt, ge_iff_le, mem_set_of_eq] at * ,
      by_contradiction hcontra ,
      rw not_le at hcontra ,
      have wrong_way := plot x hcontra ,
      linarith , } ,
  end ,
  mble := begin
    intros n ,
    apply (@indic_mble_iff α (borel(α)) (thickening_o (δseq(n)) E)).mpr ,
    apply open_imp_borel ,
    exact is_open_thickening_o ,
  end ,
}


lemma approx_indicator_seq_thickening_o_def (E : set α) (non_emp : E.nonempty)
  (δseq : ℕ → ℝ) (hpos : ∀ n , 0 < δseq(n)) 
  (hdecr : is_decreasing_seq δseq) (hlim : lim_R δseq 0) :
    (approx_indicator_seq_thickening_o E non_emp δseq hpos hdecr hlim).funseq 
    = (λ n , (indic (thickening_o (δseq(n)) E)))
      := by refl


lemma compl_union_infdist_level_sets (E : set α)
  (non_emp_E : E.nonempty) (closed_E : is_closed E) :
  Eᶜ = ⋃ (δ ∈ { δ' : ℝ | δ'>0}) , {x : α | ((inf_dist x E) = δ) } :=
begin
  ext x ,
  simp only [exists_prop, mem_Union, gt_iff_lt, mem_set_of_eq, exists_eq_right', mem_compl_eq] ,
  apply not_iff_not.mp ,
  simp only [not_lt, not_not_mem] ,
  rw ← closure_eq_iff_is_closed.mpr closed_E ,
  have dist_zero_cond : inf_dist x (closure E) ≤ 0 ↔ inf_dist x E = 0 ,
  { rw inf_dist_eq_closure ,
    have id_nn : inf_dist x E ≥ 0 := inf_dist_nonneg ,
    exact has_le.le.le_iff_eq id_nn , } ,
  rw dist_zero_cond ,
  exact mem_closure_iff_inf_dist_zero non_emp_E ,
end


lemma countably_many_infdist_level_sets_of_positive_measure
  (μ : @measure_theory.measure α (borel α)) [hfin : @probability_measure α (borel(α)) μ] (E : set α) :
    set.countable {δ : ℝ | δ > 0 ∧ μ {x : α | ((inf_dist x E) = δ) } > 0 } :=
begin
  have cont_dist := continuous_inf_dist_pt E ,
  have mble_dist := continuous.borel_measurable cont_dist ,
  set d := (λ x , inf_dist x E) with hd ,
  have sub : {δ : ℝ | δ > 0 ∧ μ ({x : α | inf_dist x E = δ}) > 0} ⊆ {y : ℝ | μ ( d⁻¹' {y}) > 0} ,
  { rintros δ ⟨ δ_pos , posmeas_δ ⟩ ,
    exact posmeas_δ , } ,
  apply countable.mono sub ,
  exact countably_many_level_sets_of_positive_measure _ mble_dist μ hfin ,
end


lemma frontier_thickening_c  (E : set α) (δ : ℝ) (δ_pos : 0 < δ) :
  frontier (thickening_c δ E) ⊆ {x : α | ((inf_dist x E) = δ) } :=
begin
  have cont := continuous_inf_dist_pt E ,
  set f := (λ x , inf_dist x E) with hf ,
  have lhs_preim : thickening_c δ E = f⁻¹' (Iic δ) := thickening_c_preimage ,
  rw lhs_preim ,
  have frontier_preim := @frontier_preimage α ℝ _ _ (Iic δ) f cont ,
  have frontier_interval : frontier (Iic δ) = {δ} := frontier_Iic ,
  have singleton_preim : {x : α | ((inf_dist x E) = δ) } = f⁻¹' {δ} := by refl ,
  rw [singleton_preim , ←frontier_interval ] ,
  apply frontier_preim ,
end


lemma frontier_thickening_o  (E : set α) (δ : ℝ) (δ_pos : 0 < δ) :
  frontier (thickening_o δ E) ⊆ {x : α | ((inf_dist x E) = δ) } :=
begin
  have cont := continuous_inf_dist_pt E ,
  set f := (λ x , inf_dist x E) with hf ,
  have lhs_preim : thickening_o δ E = f⁻¹' (Iio δ) := thickening_o_preimage ,
  rw lhs_preim ,
  have frontier_preim := @frontier_preimage α ℝ _ _ (Iio δ) f cont ,
  have frontier_interval : frontier (Iio δ) = {δ} := frontier_Iio ,
  have singleton_preim : {x : α | ((inf_dist x E) = δ) } = f⁻¹' {δ} := by refl ,
  rw [singleton_preim , ←frontier_interval ] ,
  apply frontier_preim ,
end


lemma closed_set_borel_proba_by_thickenings
  (μ : @measure_theory.measure α (borel α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) (clos_F : is_closed F) (nonemp : F.nonempty) (δseq : ℕ → ℝ)
  (δpos : ∀ n , δseq(n) > 0 ) (δdecr : is_decreasing_seq δseq)
  (δlim : lim_R δseq 0 ) :
    lim_enn (λ (n:ℕ) , ( μ (thickening_o (δseq(n)) F)) ) (μ(F)) := 
begin
  have F_eq_clos_F : closure F = F := is_closed.closure_eq clos_F ,
  have mble_F := closed_imp_borel clos_F ,
  have fseq_rw := approx_indicator_seq_thickening_o_def F nonemp δseq δpos δdecr δlim ,
  set appr := approx_indicator_seq_thickening_o F nonemp δseq δpos δdecr δlim with happr ,
  have f_rw : ∀ (n : ℕ) , appr.funseq n = indic (thickening_o (δseq(n)) F) ,
  { rw fseq_rw ,
    intros n ,
    refl , } ,
  have open_thick : ∀ (n : ℕ) , is_open (thickening_o (δseq(n)) F) := (λ n , is_open_thickening_o ),
  have mble_thick := (λ (n : ℕ) , open_imp_borel (open_thick n) ) ,
  have eq : (λ (n : ℕ) , @lintegral α (borel(α)) μ (appr.funseq(n)) ) = (λ (n : ℕ) , μ (thickening_o (δseq(n)) F) ) ,
  { funext n ,
    rw (f_rw n) ,
    exact integral_indic μ _ (mble_thick n) , } ,
  have fin_integr : @lintegral α (borel(α)) μ (appr.funseq(0)) < ⊤ ,
  { have eq_zero := congr_fun eq 0 ,
    dsimp at eq_zero ,
    rw eq_zero ,
    exact proba_finite μ _ , } ,
  rw ← F_eq_clos_F at mble_F ,
  have meas_eq : μ (closure F) = μ (F) := congr_arg ⇑μ F_eq_clos_F ,
  have key := measure_of_mble_decr_approx_indicator μ (closure F) mble_F appr fin_integr ,
  rwa [← eq , ← meas_eq ] ,
end


end portmanteau_metric_lemmas


end portmanteau


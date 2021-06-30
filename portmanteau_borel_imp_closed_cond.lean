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
import portmanteau_proba_lemmas
import portmanteau_topological_lemmas
import portmanteau_metric_lemmas
import portmanteau_definitions



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

section portmanteau_borel_condition_implies_closed_condition



variables {α : Type} [metric_space α]

notation `borel_measure`(α) := @measure_theory.measure α (borel α)
notation `borel_set`(α) E := (borel α).measurable_set' E


lemma exists_infdist_level_sets_of_zero_measure_with_small_level
  (a b : ℝ) (a_pos : 0 < a) (a_lt_b : a < b)
  (μ : borel_measure(α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) :
    {δ : ℝ | δ ∈ Ioo a b ∧ μ {x : α | ((inf_dist x F) = δ) } = 0 }.nonempty :=
begin
  -- TODO: It seems more appropriate to do this with uncountable cardinality,
  -- but I didn't find the relevant lemmas... This is now done instead using the
  -- stronger condition of positive Lebesgue measure. Either one works, but the
  -- former would arguably be more natural and elegant.
  have bad_small := countably_many_infdist_level_sets_of_positive_measure μ F ,
  set B' := {δ : ℝ | δ > 0 ∧ μ {x : α | ((inf_dist x F) = δ) } > 0 } with hB' ,
  set B := B' ∩ (Ioo a b) with hB ,
  have sub1 : B ⊆ B' := inter_subset_left B' (Ioo a b) ,
  have sub2 : B ⊆ (Ioo a b) := inter_subset_right B' (Ioo a b) ,
  have ctble_B : B.countable := countable.mono sub1 bad_small ,
  have mble_B : measurable_set B := countable.measurable_set ctble_B ,
  have null_B : (volume : measure ℝ) B = 0 ,
  { apply set.countable.measure_zero ctble_B ,
    exact real.has_no_atoms_volume , } ,  
  have Ioo_large : (volume : measure ℝ) (Ioo a b) > 0 ,
  { rw @volume_Ioo a b ,
    simp only [a_lt_b, ennreal.of_real_pos, gt_iff_lt, sub_pos] , } ,
  have compl : {δ : ℝ | δ ∈ Ioo a b ∧ μ {x : α | ((inf_dist x F) = δ) } = 0 } = (Ioo a b) \ B ,
  { apply le_antisymm ,
    { intros δ hδ ,
      have notbad : δ ∉ B ,
      { by_contradiction pretendbad ,
        exact ne_of_gt pretendbad.1.2 hδ.2 , } ,
      exact ⟨ hδ.1 , notbad ⟩ , } ,
    { intros δ hδ ,
      have δ_in_Ioo : δ ∈ Ioo a b := mem_of_mem_diff hδ ,
      have δ_pos : 0 < δ := lt_trans a_pos δ_in_Ioo.1 ,
      have good : δ ∉ B := not_mem_of_mem_diff hδ ,
      have good' : δ ∉ B' ,
      { by_contradiction nogood' ,
        have in_B : δ ∈ B := mem_inter nogood' δ_in_Ioo ,
        contradiction , } ,
      have key : μ {x : α | inf_dist x F = δ} = 0 ,
      { by_contradiction hcontra ,
        have pos_meas : 0 < μ {x : α | inf_dist x F = δ} ,
        { have meas_ne_zero : μ {x : α | inf_dist x F = δ} ≠ 0 := hcontra ,
          have meas_ge_zero : 0 ≤ μ {x : α | inf_dist x F = δ} := zero_le _ ,
          apply lt_iff_le_and_ne.mpr ⟨meas_ge_zero , meas_ne_zero.symm⟩ , } ,
        exact good' ⟨δ_pos , pos_meas⟩ , } ,
      exact ⟨δ_in_Ioo , key⟩ , } ,
  } ,
  rw compl ,
  clear compl hB ,
  have Ioo_minus_large : (volume : measure ℝ) ((Ioo a b) \ B) > 0 ,
  { suffices : (volume : measure ℝ) ((Ioo a b) \ B) = (volume : measure ℝ) (Ioo a b) ,
    { rwa this , } ,
    have mdiff := @measure_diff ℝ _ (volume : measure ℝ) _ _ sub2 (measurable_set_Ioo) mble_B (by simp [null_B]) ,
    rwa [mdiff, null_B] ,
    simp only [ennreal.sub_zero] , } , 
  by_contradiction hcontra ,
  have emp : ((Ioo a b) \ B) = ∅ := set.not_nonempty_iff_eq_empty.mp hcontra ,
  rw emp at Ioo_minus_large ,
  simp only [measure_empty, ennreal.not_lt_zero, gt_iff_lt] at Ioo_minus_large ,
  contradiction ,
end


private lemma reciprocal_lt (n : ℕ) : (1/(n+2) : ℝ) < (1/(n+1) : ℝ) :=
begin
  have decr : ∀ (x y : ℝ) , 0 < x → x < y → 1/y < 1/x ,
  { intros x y ,
    exact one_div_lt_one_div_of_lt , } ,
  have pos : 0 < ((n+1) : ℝ) := nat.cast_add_one_pos n ,
  have lt' : (n+1) < (n+2) := lt_add_one (n+1) ,
  have lt : (n+1 : ℝ) < (n+2 : ℝ) ,
  {simp at * , norm_cast , exact dec_trivial , } ,
  exact decr (n+1) (n+2) pos lt ,
end


private def seq_of_good_radii
  (μ : borel_measure(α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) : ℕ → ℝ :=
    λ n , classical.some (exists_infdist_level_sets_of_zero_measure_with_small_level (1/(n+2) : ℝ) ((1/(n+1)) : ℝ) (by tidy) (reciprocal_lt n) μ F)


private lemma seq_of_good_radii_decr
  (μ : borel_measure(α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) : is_decreasing_seq (seq_of_good_radii μ F) :=
begin
  set s := (seq_of_good_radii μ F) with hs ,
  intros n m hnm ,
  by_cases h : n = m ,
  { rw h , } ,
  { have n_succ_le_m : n+1 ≤ m := nat.succ_le_iff.mpr ((ne.le_iff_lt h).mp hnm) ,
    have key_le : (1/(m+1) : ℝ) ≤ (1/(n+2) : ℝ) ,
    { have n_succ_le_m' : (n+2 : ℝ) ≤ (m+1 : ℝ) ,
      { norm_cast , 
        exact nat.succ_le_succ n_succ_le_m , } ,
      apply one_div_le_one_div_of_le _ n_succ_le_m' ,
      norm_cast , 
      exact dec_trivial , } , 
    have lbn : (1/(n+2) : ℝ) < s n
      := (some_spec (exists_infdist_level_sets_of_zero_measure_with_small_level (1/(n+2) : ℝ) ((1/(n+1)) : ℝ) (by tidy) (reciprocal_lt n) μ F)).1.1 ,
    have ubm : s m < (1/(m+1) : ℝ) 
      := (some_spec (exists_infdist_level_sets_of_zero_measure_with_small_level (1/(m+2) : ℝ) ((1/(m+1)) : ℝ) (by tidy) (reciprocal_lt m) μ F)).1.2 ,
    have key := lt_trans (lt_of_lt_of_le ubm key_le) lbn ,
    exact le_of_lt key , } ,
end


private lemma seq_of_good_radii_pos
  (μ : borel_measure(α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) : 
    ∀ (n : ℕ) , 0 < (seq_of_good_radii μ F n) :=
begin
  set s := (seq_of_good_radii μ F) with hs ,
  intros n ,
  have lbn : (1/(n+2) : ℝ) < s n
    := (some_spec (exists_infdist_level_sets_of_zero_measure_with_small_level (1/(n+2) : ℝ) ((1/(n+1)) : ℝ) (by tidy) (reciprocal_lt n) μ F)).1.1 ,
  have pos : 0 < (1/(n+2) : ℝ) ,
  { simp only [one_div , inv_pos] ,
    norm_cast, 
    exact dec_trivial , } ,
  linarith ,
end


private lemma seq_of_good_radii_tendsto
  (μ : borel_measure(α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) : lim_R (seq_of_good_radii μ F) 0 :=
begin
  have posseq := seq_of_good_radii_pos μ F ,
  set s := (seq_of_good_radii μ F) with hs ,
  have ub : ∀ (n : ℕ) , s(n) < 1/(n+1)
    := λ n , (some_spec (exists_infdist_level_sets_of_zero_measure_with_small_level (1/(n+2) : ℝ) ((1/(n+1)) : ℝ) (by tidy) (reciprocal_lt n) μ F)).1.2 ,
  apply squeeze_zero (λ n , le_of_lt (posseq n)) (λ n , le_of_lt (ub n)) ,
  exact tendsto_one_div_add_at_top_nhds_0_nat ,
end


private lemma seq_of_good_radii_null
  (μ : borel_measure(α)) [hfin : @probability_measure α (borel(α)) μ]
  (F : set α) : 
  ∀ (n : ℕ) , μ {x : α | inf_dist x F = seq_of_good_radii μ F n } = 0 :=
begin
  set s := (seq_of_good_radii μ F) with hs ,
  intros n ,
  exact (some_spec (exists_infdist_level_sets_of_zero_measure_with_small_level (1/(n+2) : ℝ) ((1/(n+1)) : ℝ) (by tidy) (reciprocal_lt n) μ F)).2 ,
end


lemma portmanteau_borel_imp_closed
  (μseq : ℕ → @measure_theory.measure α (borel α)) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : @measure_theory.measure α (borel α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
  portmanteau_borel μseq μ → portmanteau_closed μseq μ :=
begin
  intros hborcond F hFclos ,
  by_cases emp : F = ∅ ,
  { rw emp ,
    simp only [measure_empty, nonpos_iff_eq_zero] ,
    exact limsup_const 0 , } ,
  have nonemp : F.nonempty := ne_empty_iff_nonempty.mp emp ,
  set δseq := (seq_of_good_radii μ F) with hs ,
  suffices : ∀ (c : ennreal) , μ(F) < c → limsup_enn (λ n , (μseq n)(F)) ≤ c ,
  { exact le_of_forall_le_of_dense this , } , 
  intros c hc ,
  set thick := λ (j : ℕ) , thickening_o (δseq(j)) F with hthick ,
  have closeenough : ∃ (j : ℕ) , μ (thick(j)) ≤ c ,
  { have approx := closed_set_borel_proba_by_thickenings μ F hFclos nonemp 
      δseq (seq_of_good_radii_pos μ F) (seq_of_good_radii_decr μ F) (seq_of_good_radii_tendsto μ F) ,
    have near := approx (Iic_mem_nhds hc) ,
    simp at near ,
    cases near with j hj ,
    use j ,
    apply hj j (by refl) , } ,
  cases closeenough with j hj ,
  have δpos : δseq(j) > 0 := seq_of_good_radii_pos μ F j ,
  have nullfrontier : μ (frontier (thick(j))) = 0 ,
  { have meas_mono := @measure_mono α (borel(α)) μ _ _ (frontier_thickening_o F (δseq(j)) δpos) ,
    rw (seq_of_good_radii_null μ F j) at meas_mono ,
    rw hthick ,
    apply le_antisymm ,
    { exact meas_mono , } ,
    simp only [zero_le] , } ,
  have openthick : is_open (thick j) := is_open_thickening_o , 
  have limthick := hborcond (thick j) (open_imp_borel openthick) (nullfrontier) ,
  have limsupthick := lim_eq_limsup_ennreal (limthick) ,
  have key_le : ∀ (n : ℕ) , (μseq(n))(F) ≤ (μseq(n))(thick j) ,
  { intros n,
    rw hthick ,
    have sub := closure_subset_thickening_o (δseq(j)) δpos F ,
    rw closure_eq_iff_is_closed.mpr hFclos at sub ,
    exact @measure_mono α (borel(α)) (μseq(n)) _ _ sub , } ,
  have limsup_le := limsup_enn_mono key_le ,
  rw limsupthick at limsup_le ,
  exact le_trans limsup_le hj ,
end



end portmanteau_borel_condition_implies_closed_condition

end portmanteau


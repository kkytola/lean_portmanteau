/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import tactic 
import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.borel_space
import topology.metric_space.basic
import topology.instances.real
import topology.instances.ennreal
import topology.instances.nnreal
import order.liminf_limsup
import portmanteau_comeonlean_lemmas
import portmanteau_definitions
import portmanteau_limsup_lemmas
import portmanteau_proba_lemmas
import portmanteau_integrals
import portmanteau_topological_lemmas
import portmanteau_metric_lemmas



noncomputable theory
open set 
open classical
open measure_theory
open measurable_space
open metric_space
open metric
open borel_space
open filter
open order
open_locale topological_space ennreal big_operators


namespace portmanteau

section portmanteau_continuous_implies_closed



structure ptwise_decr_bdd_cont_lim_ennreal {β : Type*} [topological_space β] (f : β → ennreal) 
    extends (ptwise_decr_lim_ennreal f) :=
  (cont : ∀ (n : ℕ) , continuous (funseq(n)) )
  (bdd : bdd_ennval (funseq(0)) )


def mble_of_ptwise_decr_bdd_cont_lim_ennreal {β : Type*} [topological_space β] {f : β → ennreal}
  (fs : ptwise_decr_bdd_cont_lim_ennreal f) : (@ptwise_decr_mble_lim_ennreal β (borel(β)) f) :=
{
  funseq := fs.funseq ,
  decr := fs.decr ,
  limit := fs.limit ,
  mble := begin
    intros n ,
    exact continuous.borel_measurable (fs.cont n) ,
  end ,
}


lemma bdd_ennval_of_ptwise_decr_bdd_cont_lim_ennreal
  {β : Type*} [topological_space β] {f : β → ennreal}
  (fs : ptwise_decr_bdd_cont_lim_ennreal f) :
    ∀ (n : ℕ) , bdd_ennval (fs.funseq(n)) :=
begin
  intros n ,
  have zero_le_n : 0 ≤ n := dec_trivial ,
  have le := is_decreasing_seq_iff.mp fs.decr 0 n zero_le_n ,
  exact bdd_ennval_of_le_bdd_ennval le fs.bdd ,
end


def pw_lin_on_thickening {α : Type*} [metric_space α]
  (δ : ℝ) (δpos : 0 < δ) (F : set α) : α → ennreal :=
    λ (x : α) , (1:ennreal) - ennreal.of_real((inf_dist x F)/δ) 


example {β : Type*} [topological_space β] (f g : β → ennreal)
  (hf : continuous f) (hg : continuous g) :
    continuous (f+g) :=
begin
  exact continuous.add hf hg ,
end


example {β : Type*} [topological_space β] (f g : β → ℝ)
  (hf : continuous f) (hg : continuous g) :
    continuous (f-g) :=
begin
  exact continuous.sub hf hg ,
end


lemma ennreal_of_real_cont : continuous (λ (x : ℝ) , ennreal.of_real x) :=
begin
  exact ennreal.continuous_of_real ,
end


lemma continuous_sub_ennreal {β : Type*} [topological_space β] (f g : β → ennreal)
  (hf : continuous f) (hg : continuous g) (hg_fin : ∀ x , g(x) ≠ ⊤ ) :
    continuous (f-g) :=
begin
  have sub_cont_on := continuous_sub_ennreal_ennreal_snd_ne_top ,
  set sub := (λ p : ennreal × ennreal, p.1 - p.2) with h_sub ,
  set fg : β → ennreal × ennreal := λ (x : β) , ⟨ f(x) , g(x) ⟩ with h_fg ,
  have eq : f-g = sub ∘ fg := by refl ,
  rw eq ,
  exact continuous_on.comp_continuous sub_cont_on (continuous.prod_mk hf hg) hg_fin ,
end


lemma continuous_add_ennreal {β : Type*} [topological_space β] (f g : β → ennreal)
  (hf : continuous f) (hg : continuous g) :
    continuous (f+g) :=
begin
  exact continuous.add hf hg ,
end


lemma pw_lin_on_thickening_cont {α : Type*} [metric_space α]
  (δ : ℝ) (δpos : 0 < δ) (F : set α) :
    continuous (pw_lin_on_thickening δ δpos F) :=
begin
  apply continuous_sub_ennreal ,
  { exact continuous_const , } , 
  { have cont : continuous (λ x , (inf_dist x F)/δ) := continuous.div_const (continuous_inf_dist_pt F) ,
    exact cont_enn_of_cont_R (λ (x : α), inf_dist x F / δ) cont , } ,
  { intros x ,
    exact ennreal.of_real_ne_top , } ,
end


lemma indic_le_pw_lin_on_thickening {α : Type*} [metric_space α]
  (δ : ℝ) (δpos : 0 < δ) (F : set α) :
    indic F ≤ pw_lin_on_thickening δ δpos F  :=
begin
  intros x ,
  by_cases hxF : x ∈ F ,
  { unfold pw_lin_on_thickening ,
    rw inf_dist_zero_of_mem hxF ,
    simp only [ennreal.sub_zero, zero_div, ennreal.of_real_zero] ,
    exact indic_le_one F x , } ,
  { have indiczero : indic F x = 0 := (indic_val_zero_iff F x).mpr hxF ,
    simp [indiczero] , } ,
end


lemma pw_lin_on_thickening_le_indic_thickening {α : Type*} [metric_space α]
  (δ : ℝ) (δpos : 0 < δ) (F : set α) :
    pw_lin_on_thickening δ δpos F ≤ indic (thickening_o δ F) :=
begin
  intros x ,
  by_cases hxFth : x ∈ thickening_o δ F ,
  { have indicone := (indic_val_one_iff (thickening_o δ F) x).mpr hxFth ,
    unfold pw_lin_on_thickening ,
    rw indicone ,
    simp ,
    exact le_self_add_ennreal _ _ , } ,
  { have dist_ge : δ ≤ inf_dist x F ,
    { simp at hxFth ,
      exact hxFth , } ,
    have dist_per_delta_ge : 1 ≤ (inf_dist x F) / δ ,
    { have key := (div_le_div_right δpos).mpr dist_ge ,
      rwa div_self (ne_of_gt δpos) at key , } ,
    have dist_per_delta_ge' : (1 : nnreal) ≤ ((inf_dist x F) / δ).to_nnreal ,
    { have key := real.to_nnreal_mono dist_per_delta_ge ,
      rwa real.to_nnreal_one at key , } ,
    have dist_per_delta_ge'' : (1 : ennreal) ≤ ennreal.of_real((inf_dist x F) / δ) ,
    { exact ennreal.coe_le_coe.mpr dist_per_delta_ge' , } , 
    have pw_lin_zero : pw_lin_on_thickening δ δpos F x = 0 ,
    { unfold pw_lin_on_thickening ,
      apply sub_larger_ennreal _ _ dist_per_delta_ge'' , } ,
    rw pw_lin_zero ,
    simp only [zero_le] , } , 
end


lemma measure_of_cont_bdd_decr_approx_indicator
  {β : Type*} [topo_β : topological_space β]
  {E : set β} (hE : (borel β).measurable_set' E)
  (fseq : ptwise_decr_bdd_cont_lim_ennreal (indic E))
  (μ : @measure_theory.measure β (borel β))
  [hfin : @probability_measure β (borel(β)) μ] :
    lim_enn (λ n , (@lintegral β (borel(β)) μ (fseq.funseq(n)))) (μ(E)) :=
begin
  have finite_integral : @lintegral β (borel(β)) μ  (fseq.funseq(0)) < ⊤
    := finite_integral_of_bdd_ennrealval μ (fseq.funseq(0)) fseq.bdd , 
  have mble_funs : ∀ n , @measurable β ennreal (borel(β)) _ (fseq.funseq(n)) ,
  { intros n ,
    exact continuous.borel_measurable (fseq.cont n) , } ,
  exact @measure_of_mble_decr_approx_indicator β (borel(β)) μ E hE (mble_of_ptwise_decr_bdd_cont_lim_ennreal fseq) finite_integral ,
end


@[class] def has_cont_decr_approx_of_closed (β : Type*) [topo_β : topological_space β] : Prop :=
  ∀ (F : set β) , is_closed F → ( ∃ (fseq : ptwise_decr_bdd_cont_lim_ennreal (indic F)) , true )


lemma one_div_nat_decr : is_decreasing_seq (λ (n : ℕ) , (1/(n+1) : ℝ)) :=
begin
  intros n m hnm ,
  exact @nat.one_div_le_one_div ℝ _ n m hnm ,
end


lemma one_div_nat_lim : lim_R (λ (n : ℕ) , (1/(n+1) : ℝ)) 0 :=
begin
  exact tendsto_one_div_add_at_top_nhds_0_nat ,
end


private def metric_ptwise_decr_bdd_cont_approx_of_nonempty_closed
  (α : Type*) [met_α : metric_space α] (F : set α) (Fclos : is_closed F) (Fnonemp : F.nonempty) :
    ptwise_decr_bdd_cont_lim_ennreal (indic F) :=
{
  funseq := λ (n : ℕ) , pw_lin_on_thickening (1/(n+1) : ℝ) (nat.one_div_pos_of_nat) F ,
  decr := begin
    intros n m hnm x ,
    dsimp ,
    unfold pw_lin_on_thickening ,
    suffices : ennreal.of_real ((inf_dist x F) / (1/(n+1) : ℝ)) ≤ ennreal.of_real ((inf_dist x F) / (1/(m+1) : ℝ)) ,
    { apply self_sub_le_self_sub_ennreal ,
      exact this , } ,
    apply ennreal.coe_le_coe.mpr ,
    apply real.to_nnreal_mono ,
    have eq : ∀ (k : ℕ) , (1/(k+1) : ℝ)⁻¹  = (k+1) := by simp ,
    have eq' : ∀ (k : ℕ) , ∀ (x : ℝ) , x / (1/(k+1) : ℝ) = x * (k+1) ,
    { intros k x ,
      rw [div_eq_mul_inv, eq k] , } ,
    rw [eq' n (inf_dist x F) , eq' m (inf_dist x F) ] ,
    have hnm' : ((n:ℝ)+1) ≤ ((m:ℝ)+1) := by simp [hnm] ,
    exact @mul_le_mul _ _ (inf_dist x F) _ (inf_dist x F) _ (rfl.ge) hnm' (by tidy) (inf_dist_nonneg) ,
  end ,
  limit := begin
    set s := λ (n : ℕ) , pw_lin_on_thickening (1/(n+1) : ℝ) (nat.one_div_pos_of_nat) F with hs ,
    intros x ,
    have seq_le : ∀ n , s n x ≤ indic (thickening_o (1/(n+1) : ℝ) F) x 
      := λ n , pw_lin_on_thickening_le_indic_thickening (1/(n+1) : ℝ) (nat.one_div_pos_of_nat) F x , 
    have seq_ge : ∀ n , indic F x ≤ s n x 
      := λ n , indic_le_pw_lin_on_thickening (1/(n+1) : ℝ) (nat.one_div_pos_of_nat) F x , 
    have lim_ub : lim_enn (λ n , indic (thickening_o (1/(n+1) : ℝ) F) x) (indic F x) ,
    { set s' := approx_indicator_seq_thickening_o F Fnonemp
          (λ n , (1/(n+1) : ℝ)) (λ n , nat.one_div_pos_of_nat) one_div_nat_decr 
          (tendsto_one_div_add_at_top_nhds_0_nat) with hs' ,
      have key := s'.limit x ,
      have F_eq_clos_F := is_closed.closure_eq Fclos ,
      have indic_eq_x : indic F x = indic (closure(F)) x 
        := by refine congr_fun (congr_arg indic (eq.symm F_eq_clos_F)) x ,
      rwa ← indic_eq_x at key , } , 
    have lim_lb : lim_enn (λ n , indic F x) (indic F x) := tendsto_const_nhds ,
    have tada := tendsto_of_tendsto_of_tendsto_of_le_of_le lim_lb lim_ub seq_ge seq_le ,
    exact tada ,
  end ,
  cont := begin
    intros n ,
    exact pw_lin_on_thickening_cont (1 / (↑n + 1)) nat.one_div_pos_of_nat F ,
  end ,
  bdd := begin
    use 1 ,
    intros x ,
    dsimp ,
    simp only [zero_add, div_one] ,
    have wow := pw_lin_on_thickening_le_indic_thickening 1 (by linarith) F ,
    apply le_trans (wow x) _ ,
    exact indic_le_one _ _ ,
  end ,
}


private def metric_ptwise_decr_bdd_cont_approx_of_empty
  (α : Type*) [met_α : metric_space α] :
    ptwise_decr_bdd_cont_lim_ennreal (indic (∅ : set α)) :=
{
  funseq := λ (n : ℕ) , 0 ,
  decr := begin
    intros n m hnm ,
    simp only [le_refl] ,
  end ,
  limit := begin
    intros x ,
    rw (indic_val_zero_iff (∅ : set α) x).mpr (by simp) ,
    apply tendsto_const_nhds ,
  end ,
  cont := begin
    intros n ,
    exact @continuous_const α ennreal _ _ 0 ,
  end ,
  bdd := begin
    use 0 ,
    intros x ,
    dsimp ,
    simp only [le_refl] ,
  end ,
}


private def metric_ptwise_decr_bdd_cont_approx_of_closed
  (α : Type*) [met_α : metric_space α] (F : set α) (Fclos : is_closed F) :
    ptwise_decr_bdd_cont_lim_ennreal (indic F) :=
begin
  by_cases hF : F = ∅ ,
  { rw hF ,
    exact metric_ptwise_decr_bdd_cont_approx_of_empty α , } , 
  { exact metric_ptwise_decr_bdd_cont_approx_of_nonempty_closed α F Fclos (ne_empty_iff_nonempty.mp hF) , } , 
end


lemma metric_space_has_cont_approx_of_closed (α : Type*) [met_α : metric_space α] :
  has_cont_decr_approx_of_closed α :=
begin
  intros F F_clos ,
  use metric_ptwise_decr_bdd_cont_approx_of_closed α F F_clos ,
end


lemma portmanteau_continuous_imp_closed_cond
  {β : Type*} {topo_β : topological_space β}
  [appr_closed : has_cont_decr_approx_of_closed β]
  (μseq : ℕ → (@measure_theory.measure β (borel β))) (μseq_fin : ∀ n , @probability_measure β (borel(β)) (μseq(n)))
  (μ : (@measure_theory.measure β (borel β))) (μ_fin : @probability_measure β (borel(β)) μ) : 
    (portmanteau_continuous_ennval μseq μ) → portmanteau_closed μseq μ :=
begin
  intros hcontcond ,
  intros F hFclosed ,
  specialize appr_closed F hFclosed ,
  cases appr_closed with fseq ,
  suffices : (∀ (ε : nnreal) (ε_pos : 0<ε) ,
      limsup_enn (λ n , (μseq(n))(F)) ≤ (μ(F)) + ε) ,
  { apply ennreal.le_of_forall_pos_le_add ,
    intros ε ε_pos unnecessary ,
    exact this ε ε_pos , } ,
  intros ε ε_pos ,
  have meas_approx' : lim_enn (λ (j : ℕ) , @lintegral β (borel(β)) μ (fseq.funseq(j)) ) (μ(F)) , 
  { apply measure_of_mble_decr_approx_indicator μ F (closed_imp_borel hFclosed)
          (mble_of_ptwise_decr_bdd_cont_lim_ennreal fseq ) _ ,
    exact @bdd_integral_of_bdd_ennval β (borel(β)) μ μ_fin (fseq.funseq(0)) fseq.bdd , } , 
  have meas_approx : ∃ (j₀ : ℕ) , @lintegral β (borel(β)) μ (fseq.funseq(j₀)) ≤ (μ(F)) + ε , 
  { change ∃ (j₀ : ℕ) , @lintegral β (borel(β)) μ (fseq.funseq(j₀)) ∈ Iic (μ(F)+ε) ,
    have lt_plus_eps := lt_add_pos_ennreal (μ(F)) ε (ennreal_lt_top_of_ne_top _ (proba_finite μ F)) (by simp [ε_pos]) ,
    have nbhd : Iic (μ(F)+ε) ∈ 𝓝(μ(F)) := Iic_mem_nhds lt_plus_eps ,
    have eventually := (filter.tendsto_at_top'.mp meas_approx') _ nbhd ,
    cases eventually with j₀ hj₀ ,
    use j₀ ,
    exact hj₀ j₀ (by simp only [ge_iff_le]) , } , 
  cases meas_approx with j hj ,
  have lim_integr :=
    hcontcond (fseq.funseq(j)) (fseq.cont(j)) (bdd_ennval_of_ptwise_decr_bdd_cont_lim_ennreal fseq j) ,
  have meas_seq_le : (∀ n , ((μseq(n)) F) ≤ (@lintegral β (borel(β)) (μseq(n)) (fseq.funseq(j)) )) ,
  { intros n ,
    have lim_le : indic F ≤ fseq.funseq(j) ,
    { intros x ,
      have decr_at_x : is_decreasing_seq (λ (n : ℕ) , ((fseq.funseq(n))(x)) ) ,
      { intros n m hnm ,
        dsimp ,
        exact fseq.decr hnm x , } , 
      have lim_at_x : lim_enn (λ (n : ℕ) , ((fseq.funseq(n))(x)) ) (indic F x) := fseq.limit x ,
      exact lim_le_of_decr (λ (n : ℕ) , ((fseq.funseq(n))(x)) ) (indic F x) decr_at_x (fseq.limit x) j , } ,
    have int_mono := @lintegral_mono β (borel(β)) (μseq(n)) _ _ lim_le ,
    rwa integral_indic (μseq(n)) F (closed_imp_borel hFclosed) at int_mono , } , 
  apply le_trans (limsup_enn_mono meas_seq_le) ,
  suffices : limsup_enn (λ (n : ℕ), @lintegral β (borel(β)) (μseq(n)) (fseq.to_ptwise_decr_lim_ennreal.funseq j)) = @lintegral β (borel(β)) μ (fseq.to_ptwise_decr_lim_ennreal.funseq j) ,
  { rwa this , } ,
  exact tendsto.limsup_eq lim_integr ,
end



end portmanteau_continuous_implies_closed

end portmanteau

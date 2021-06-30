/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import portmanteau_definitions
import portmanteau_topological_lemmas
import portmanteau_proba_lemmas
import portmanteau_open_equiv_closed
import portmanteau_integrals
import measure_theory.measurable_space
import measure_theory.integration
import measure_theory.borel_space
import measure_theory.lebesgue_measure



noncomputable theory
open set
open topological_space
open measure_theory
open real
open ennreal


namespace portmanteau

section portmanteau_open_implies_continuous



variables {α : Type} [topological_space α]


-- Why define `real_lt_ennreal`?
-- Note that `ennreal.of_real ((-42 : ℝ)) = (0 : ennreal)` but we want `(-42 : ℝ) < (0 : ennreal)`
-- and `(37 : ℝ) > (∞ : ennreal).to_real` but we want `(37 : ℝ) < (∞ : ennreal)`.
abbreviation real_lt_ennreal (x : ℝ) (z : ennreal) : Prop :=
  (z = ⊤) ∨ (x < ennreal.to_real(z))


lemma real_lt_ennreal_of_le {x y : ℝ} {z : ennreal} (hxy : x ≤ y) (hyz : real_lt_ennreal y z) :
  real_lt_ennreal x z :=
begin
  cases hyz ,
  { left , 
    exact hyz , } ,
  { right , 
    exact lt_of_le_of_lt hxy hyz , } ,
end

lemma real_lt_ennreal_ne_top_iff (x : ℝ) (z : ennreal) (hz : z ≠ ⊤) :
  real_lt_ennreal x z ↔ x < ennreal.to_real(z) :=
begin
  split ,
  { intros h ,
    cases h ,
    { contradiction , } ,
    { exact h , } , 
  } ,
  { intros h ,
    right ,
    exact h , } ,
end


lemma real_lt_ennreal_ne_top_iff' (x : ℝ) (z : ennreal) (hx : 0 ≤ x) (hz : z ≠ ⊤) :
  real_lt_ennreal x z ↔ ennreal.of_real x < z :=
begin
  rw real_lt_ennreal_ne_top_iff x z hz ,
  exact (of_real_lt_iff_lt_to_real hx hz).symm ,
end


-- Remark: It would feel more mathematically natural to define, for `g : β → ennreal`,
-- the set `below_graph_ennval g` as a subset of `β × nnreal`, but since there was
-- no Lebesgue measure on `nnreal`, I ended up using 
-- `(volume.restrict {t : ℝ | 0 < t} : measure ℝ)` instead, and therefore the following...
def below_graph_ennval {β : Type*} (g : β → ennreal) := { bt : β × ℝ | real_lt_ennreal (bt.2) (g(bt.1)) }


lemma mble_piece_below_graph {β : Type*} [measurable_space β] (g : β → ennreal) [hg : measurable g] :
  ∀ (r : ℝ) , measurable_set { bt : β × ℝ | bt.2 ≤ r ∧ real_lt_ennreal r (g(bt.1)) } :=
begin
  intro r ,
  have asprod : { bt : β × ℝ | bt.2 ≤ r ∧ real_lt_ennreal r (g(bt.1)) } = set.prod {b : β | real_lt_ennreal r (g b) } (Iic r) ,
  { ext bt ,
    simp only [mem_set_of_eq, mem_prod, mem_Iic] ,
    exact and.comm , } ,
  have interval_mble : measurable_set (Iic r) := measurable_set_Iic ,
  have preimage_mble : measurable_set { b : β | real_lt_ennreal r (g b) } ,
  { by_cases hr : 0 ≤ r ,
    { have as_preim : { b : β | real_lt_ennreal r (g b) } = g⁻¹' (Ioi (ennreal.of_real r)) ,
      { ext b ,
        simp only [mem_set_of_eq, mem_Ioi, mem_preimage] ,
        by_cases gb_top : g b = ⊤ ,
        { have h₁ : real_lt_ennreal r (g b) := by {left , exact gb_top , } ,
          have h₂ : ennreal.of_real r < (g b) := by { rw gb_top , exact of_real_lt_top , } ,
          simp only [h₁, h₂] , } ,
        { exact real_lt_ennreal_ne_top_iff' _ _ hr gb_top , } ,
      } ,
      rw as_preim ,
      apply hg ,
      exact measurable_set_Ioi , } ,
    { have eq_all : { b : β | real_lt_ennreal r (g b) } = univ ,
      { ext b ,
        simp only [mem_univ, mem_set_of_eq, iff_true] ,
        right ,
        exact lt_of_lt_of_le (not_le.mp hr) (@ennreal.to_real_nonneg (g(b))) , } ,
      rw eq_all ,
      exact measurable_set.univ , } ,
  } ,
  have mble_prod := measurable_set.prod preimage_mble interval_mble , 
  exact measurable_set.congr mble_prod (eq.symm asprod) ,
end


lemma below_graph_ennval_union {β : Type*} [measurable_space β]
  (g : β → ennreal) [hg : measurable g] (S : set ℝ) (hSdense : dense S):
  below_graph_ennval g = ( ⋃ (r : S) , { bt : β × ℝ | bt.2 ≤ r ∧ real_lt_ennreal r (g(bt.1)) } ) :=
begin
  ext bt ,
  rw mem_Union ,
  split ,
  { intro hbt ,
    have midpt : ∃ (t : S) , (bt.snd < t) ∧ real_lt_ennreal t (g(bt.fst)) , 
    { have opn₁ : is_open {t' : ℝ | bt.snd < t'} := is_open_lt' bt.snd ,
      have opn₂ : is_open {t' : ℝ | real_lt_ennreal t' (g(bt.fst)) } ,
      { by_cases g_val_top : g(bt.fst) = ⊤ ,
        { have eq_all : {t' : ℝ | real_lt_ennreal t' (g(bt.fst)) } = univ ,
          { apply le_antisymm ,
            { intros s hs , exact dec_trivial , } ,
            { intros s hs , left , exact g_val_top , } ,
          } ,
          rw eq_all ,
          exact is_open_univ ,
        } , 
        { have setsimp : {t' : ℝ | real_lt_ennreal t' (g bt.fst)} = {t' : ℝ | t' < (g bt.fst).to_real } ,
          { ext t ,
            simp only [mem_set_of_eq] ,
            exact real_lt_ennreal_ne_top_iff t (g bt.fst) g_val_top , } ,
          lift g(bt.fst) to nnreal using g_val_top with gval hgval ,
          rw setsimp ,
          exact is_open_gt' (gval : ℝ) , } , 
        } ,
      have opn : is_open {t' : ℝ | bt.snd < t' ∧ real_lt_ennreal t' (g(bt.fst))} := is_open.and opn₁ opn₂ ,
      have nonemp : {t' : ℝ | bt.snd < t' ∧ real_lt_ennreal t' (g(bt.fst))}.nonempty ,
      { by_cases g(bt.fst) = ⊤ ,
        { use (bt.snd + 1) ,
          simp only [lt_add_iff_pos_right, mem_set_of_eq] ,
          rw h ,
          split ,
          { exact zero_lt_one , } ,
          { exact dec_trivial , } , 
        } ,
        { have hbt' := (real_lt_ennreal_ne_top_iff bt.snd _ h).mp hbt ,
          have exmid := exists_between hbt' ,
          cases exmid with c hc ,
          use c ,
          simp only [hc, true_and, mem_set_of_eq] ,
          right ,
          exact hc.2 , } ,
        } , 
      have hereitis := dense_iff_inter_open.mp hSdense _ opn nonemp ,
      rcases hereitis with ⟨ t₀ , ht₀ , hSt₀ ⟩ ,
      use [t₀ , hSt₀ , ht₀] , } , 
    cases midpt with t ht ,
    use t ,
    simp ,
    split ,
    { exact le_of_lt ht.1 , } , 
    { exact ht.2 , } ,
    } ,
  { intros hexs ,
    rcases hexs with ⟨ s , hts , hsg ⟩ , 
    apply real_lt_ennreal_of_le hts hsg , } ,
end


lemma below_graph_ennval_union' {β : Type*} [measurable_space β]
  (g : β → ennreal) [hg : measurable g] (seq : ℕ → ℝ) (hseqdense : dense (range seq)):
  below_graph_ennval g = ( ⋃ (n : ℕ) , { bt : β × ℝ | bt.2 ≤ (seq(n)) ∧ real_lt_ennreal (seq(n)) (g(bt.1)) } ) :=
begin
  have key := @below_graph_ennval_union β _ g hg (range seq) hseqdense ,
  rw key ,
  ext bt , 
  cases bt , 
  simp only [exists_prop, mem_Union, set_coe.exists, mem_range, exists_exists_eq_and, subtype.coe_mk] ,
end


lemma measurable_below_graph_ennval {β : Type*} [measurable_space β] (g : β → ennreal) [hg : measurable g] :
  measurable_set (below_graph_ennval g) :=
begin
  have key_mble := @mble_piece_below_graph β _ g hg ,
  have ex_dense_seq := topological_space.exists_dense_seq ℝ ,
  rcases ex_dense_seq with ⟨ seq , range_seq_dense ⟩ ,
  have key_mble_seq := (λ (n : ℕ) , key_mble (seq(n))) ,
  have key_union := @below_graph_ennval_union' β _ g hg seq range_seq_dense ,
  rw key_union ,
  apply measurable_set.Union key_mble_seq ,
end


lemma measurable_indicator_below_graph_ennval {β : Type*} [measurable_space β] (g : β → ennreal) [hg : measurable g] :
  measurable ( indic (below_graph_ennval g) ) :=
begin
  have key := (indic_mble_iff (below_graph_ennval g)).mpr ,
  exact key (@measurable_below_graph_ennval β _ g hg) ,
end


lemma integral_one_from_zero_to_ennreal (c : ennreal) :
  lintegral (volume : measure ℝ) (λ (t : ℝ) , indic {t : ℝ | 0 < t ∧ real_lt_ennreal t c} t ) = c :=
begin
  by_cases c_infty : c = ⊤ ,
  { have eq₀ : {t : ℝ | 0 < t ∧ real_lt_ennreal t c} = Ioi 0 ,
    { rw c_infty ,
      ext t ,      
      simp only [mem_set_of_eq, mem_Ioi, and_iff_left_iff_imp] ,
      intros t ,
      exact dec_trivial , } ,
    rw [eq₀ , c_infty] ,
    simp only [lintegral_one, measurable_set.univ, lintegral_indicator, measurable_set_Ioi, measure.restrict_apply, volume_Ioi,
  univ_inter] , } ,
  { have eq₀ : {t : ℝ | 0 < t ∧ real_lt_ennreal t c} = Ioo 0 c.to_real ,
    { ext t ,
      simp ,
      intros t_pos c_eq_top ,
      contradiction , } ,
    rw eq₀ ,
    simp ,
    exact ennreal.of_real_to_real c_infty , } ,
end


lemma crossection_one_of_below_graph_ennval {β : Type*} (g : β → ennreal) (b : β) :
  { t : ℝ | (⟨b , t⟩ : β × ℝ ) ∈ (below_graph_ennval g) } = {t : ℝ | real_lt_ennreal t (g(b))} := by refl 


lemma marginal_one_of_below_graph_ennval {β : Type*} (g : β → ennreal) (b : β) :
  lintegral (volume.restrict { t : ℝ | 0 < t} : measure ℝ) (λ t , indic (below_graph_ennval g) (⟨b,t⟩ : β × ℝ)) = g(b) :=
begin
  have crosssec := crossection_one_of_below_graph_ennval g b ,
  have eq : (λ (t : ℝ) , indic (below_graph_ennval g) (⟨b,t⟩ : β × ℝ)) = indic {t : ℝ | real_lt_ennreal t (g(b))} ,
  { rw ← (crossection_one_of_below_graph_ennval g b) ,
    refl , } ,
  rw eq ,
  by_cases h_gval : g(b) = ⊤ ,
  { rw h_gval ,
    have eq₁ : {t : ℝ | real_lt_ennreal t ⊤} = univ ,
    { ext t ,
      simp only [mem_univ, mem_set_of_eq, iff_true] ,
      left ,
      refl , } ,
    rw eq₁ ,
    rw indic_univ ,
    have vol_infty : (volume : measure ℝ) {t : ℝ | 0 < t} = ⊤ := volume_Ioi , 
    simp only [vol_infty, lintegral_one, measurable_set.univ, measure.restrict_apply, univ_inter] , } ,
  { have eq₂ : {t : ℝ | real_lt_ennreal t (g(b))} = (Iio (ennreal.to_real (g(b)))) ,
    { ext t ,
      simp only [mem_Iio, mem_set_of_eq, or_iff_right_iff_imp] ,
      intro h ,
      contradiction , } ,
    rw eq₂ ,
    have key := integral_indic (volume.restrict { t : ℝ | 0 < t} : measure ℝ) (Iio (ennreal.to_real (g(b)))) (measurable_set_Iio) ,
    rw key ,
    have set_eq : Iio (ennreal.to_real (g(b))) ∩ {t : ℝ | 0 < t} = Ioo 0 (ennreal.to_real (g(b))) ,
    { ext t ,
      simp only [mem_inter_eq, mem_Iio, mem_Ioo, mem_set_of_eq] ,
      tauto , } ,
    simp [set_eq] ,
    exact ennreal.of_real_to_real h_gval , } ,
end


lemma crossection_two_of_below_graph_ennval {β : Type*} (g : β → ennreal) (t : ℝ) (t_nn : 0 ≤ t) :
  { b : β | (⟨b , t⟩ : β × ℝ ) ∈ (below_graph_ennval g) } = g⁻¹' (Ioi (ennreal.of_real t)) :=
begin
  ext b ,
  by_cases h_gval : g b = ⊤ ,
  { simp only [h_gval, of_real_lt_top, mem_set_of_eq, mem_Ioi, iff_true, mem_preimage] ,
    left ,
    exact h_gval , } ,
  exact real_lt_ennreal_ne_top_iff' t (g(b)) t_nn h_gval ,
end


lemma crossection_two_of_below_graph_ennval' {β : Type*} (g : β → ennreal) (t : ℝ) (t_neg : t < 0 ) :
  { b : β | (⟨b , t⟩ : β × ℝ ) ∈ (below_graph_ennval g) } = univ :=
begin
  ext b ,
  simp only [mem_univ, mem_set_of_eq, iff_true] ,
  right ,
  exact lt_of_lt_of_le t_neg (to_real_nonneg) ,
end


lemma measurable_marginal_two_of_below_graph_ennval {β : Type*} [measurable_space β] (μ : measure β) [hμ : sigma_finite μ]
  (g : β → ennreal) [hg : measurable g] :
  measurable (λ (t : ℝ) , lintegral μ (λ b , indic (below_graph_ennval g) (⟨b,t⟩ : β × ℝ))) :=
begin
  have mble_fun := @measurable_indicator_below_graph_ennval _ _ g hg ,
  exact @measurable.lintegral_prod_left' β ℝ _ _ μ _ _ mble_fun ,
end


lemma marginal_two_of_below_graph_ennval {β : Type*} [measurable_space β] (μ : measure β) [hμ : sigma_finite μ]
  (g : β → ennreal) [hg : measurable g] (t : ℝ) (t_nn : 0 ≤ t) :
  lintegral μ (λ b , indic (below_graph_ennval g) (⟨b,t⟩ : β × ℝ)) = μ (g⁻¹' (Ioi (ennreal.of_real t))) :=
begin
  have crosssec := crossection_two_of_below_graph_ennval g t t_nn ,
  have eq : (λ b , indic (below_graph_ennval g) (⟨b,t⟩ : β × ℝ)) = indic (g⁻¹' (Ioi (ennreal.of_real t))) ,
  { rw ← (crossection_two_of_below_graph_ennval g t t_nn) ,
    refl , } ,
  rw eq ,
  apply integral_indic ,
  exact hg (measurable_set_Ioi) ,
end


lemma lintegral_eq_lintegral_ccdf {β : Type*} [measurable_space β]
  (μ : measure β) [hμ : sigma_finite μ] (g : β → ennreal) [hg : measurable g] :
    lintegral μ g = lintegral (volume.restrict { t : ℝ | 0 < t } : measure ℝ) (λ (t : ℝ) , μ (g ⁻¹' Ioi (ennreal.of_real t)) ) :=
begin
  set P := { t : ℝ | 0 < t } with hP ,
  set Leb_P := (volume.restrict { t : ℝ | 0 < t } : measure ℝ) with h_Leb_P ,
  have pi_mble := @measurable_indicator_below_graph_ennval β _ g hg ,
  set f := (λ (b : β) , (λ (t : ℝ) , (indic (below_graph_ennval g) (⟨b, t⟩ : β × ℝ)))) with hf ,
  have swap := @lintegral_lintegral_swap β ℝ _ _ μ Leb_P _ hμ f (measurable.ae_measurable pi_mble) ,
  have key₁ : ( λ (b : β) , lintegral (volume.restrict { t : ℝ | 0 < t } : measure ℝ) (λ (t : ℝ) , f b t)) = g ,
  { funext b ,
    exact marginal_one_of_below_graph_ennval g b , } ,
  rw key₁ at swap ,
  have key₂ : ( λ (t : ℝ) , lintegral μ (λ (b : β) , f b t)) =ᵐ[Leb_P] (λ t , (μ (g ⁻¹' (Ioi (ennreal.of_real t))))) ,
  { suffices : P ⊆ {t : ℝ | ( λ (t : ℝ) , lintegral μ (λ (b : β) , f b t)) t = (λ t , (μ (g ⁻¹' (Ioi (ennreal.of_real t))))) t} ,
    { have Pc_null : Leb_P (Pᶜ) = 0 ,
      { have Pc_eq : Pᶜ = Iic 0 ,
        { ext t , 
          dsimp ,
          simp only [not_lt, mem_Iic] , } ,
        rw [Pc_eq, h_Leb_P] ,
        have inter : Iic 0 ∩ P = ∅ ,
        { ext t , 
          dsimp , 
          simp only [imp_self, not_and, not_lt, mem_Iic, iff_false] , } ,
        simp [inter] , } , 
      exact @filter.mem_sets_of_superset ℝ (measure.ae Leb_P) P _ Pc_null this , } ,
    intros t ht ,
    exact @marginal_two_of_below_graph_ennval β _ μ hμ g hg t (le_of_lt ht) , } ,
  rwa ← (lintegral_congr_ae key₂) ,
end


lemma portmanteau_open_fatou {β : Type*} [measurable_space β] (vol : measure β)
  {Gfun : β → set α} (G_opens : ∀ b , is_open (Gfun b))
  (μseq : ℕ → @measure_theory.measure α (borel α)) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : @measure_theory.measure α (borel α)) (μ_fin : @probability_measure α (borel(α)) μ)
  (mble : ∀ (n : ℕ) , measurable (λ (b : β) , (μseq(n)) (Gfun(b)) )) : 
    portmanteau_open μseq μ →
      ( lintegral vol (λ b , μ (Gfun b)) ≤ liminf_enn (λ n , lintegral vol (λ b , (μseq(n)) (Gfun b)) )) :=
begin
  intros hopcond ,
  set f := (λ (n : ℕ) , (λ (b : β) , (μseq(n)) (Gfun(b)) ) ) with hf ,
  have fatou := @measure_theory.lintegral_liminf_le _ _ vol f mble ,
  rw hf at fatou ,
  have le_liminf : (λ (b : β) , μ (Gfun b) ) ≤ (λ (b : β) , liminf_enn (λ (n : ℕ ), (μseq(n)) (Gfun b) )) ,
  { intros b ,
    exact hopcond _ (G_opens b) , } , 
  have int_mono := @lintegral_mono β _ vol _ _ le_liminf ,
  exact le_trans int_mono fatou ,
end


lemma portmanteau_open_imp_cont_liminf
  (μseq : ℕ → @measure_theory.measure α (borel α)) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : @measure_theory.measure α (borel α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
    portmanteau_open μseq μ →
      ( ∀ (f : α → ennreal) , continuous f → bdd_ennval f →
        @lintegral α (borel(α)) μ f ≤ liminf_enn (λ n , @lintegral α (borel(α)) (μseq(n)) f ) ) :=
begin
  intros hopcond f f_cont f_bdd ,
  have f_mble := continuous.borel_measurable f_cont ,
  have preim_open : ∀ (t : ℝ) , is_open (f⁻¹' Ioi (ennreal.of_real t)) ,
  { intros t ,
    exact continuous_def.mp f_cont (Ioi (ennreal.of_real t)) (is_open_Ioi) , } ,
  have rwkey := @lintegral_eq_lintegral_ccdf α (borel α) μ _ f f_mble ,
  have rwkeyseq : (λ n , @lintegral α (borel(α)) (μseq(n)) f ) = (λ n , lintegral (volume.restrict {t : ℝ | 0 < t} : measure ℝ) (λ (t : ℝ) , (μseq(n)) (f ⁻¹' Ioi (ennreal.of_real t)) ) ) ,
  { exact funext (λ n , @lintegral_eq_lintegral_ccdf α (borel α) (μseq(n)) _ f f_mble) , } ,
  have mble_meas : ∀ n , measurable (λ t , (μseq(n)) (f⁻¹' Ioi (ennreal.of_real t)) ) ,
  { intros n ,
    have key := @measurable_marginal_two_of_below_graph_ennval α (borel(α)) (μseq(n)) _ f f_mble ,
    set P := { t : ℝ | 0 ≤ t } with hP ,
    have P_mble : measurable_set P := measurable_set_Ici ,
    set f₀ := (λ t , (μseq(n)) (f⁻¹' Ioi (ennreal.of_real t)) ) with hf₀ ,
    set f₁ := ( λ t , @lintegral α (borel(α)) (μseq(n)) (λ b , indic (below_graph_ennval f) (⟨b,t⟩ : α × ℝ))) with hf₁ ,
    set c := (μseq(n)) (f⁻¹'(Ioi (0:ennreal))) with hc ,
    set cfun := (λ (t:ℝ) , c) with hcfun ,
    have eq : f₀ = (indic P) * f₁ + (indic Pᶜ) * cfun ,
    { funext t ,
      dsimp ,
      by_cases ht : t ∈ P ,
      { rw [(indic_val_one_iff P t).mpr ht , (indic_val_zero_iff (Pᶜ) t).mpr (not_not.mpr ht)] ,
        simp only [add_zero, one_mul, zero_mul] ,
        exact (@marginal_two_of_below_graph_ennval α (borel(α)) (μseq(n)) _ f f_mble t ht).symm , } ,
      { rw [(indic_val_zero_iff P t).mpr ht , (indic_val_one_iff (Pᶜ) t).mpr (mem_compl ht)] ,
        simp only [one_mul, zero_mul, zero_add] ,
        rw [hf₀ , hcfun] ,
        dsimp ,
        rw hc ,
        have eq_Ioi : Ioi (0:ennreal) = Ioi (ennreal.of_real t) ,
        { have eq_val := ennreal.of_real_eq_zero.mpr (le_of_lt (not_le.mp ht)) ,
          exact congr_arg Ioi eq_val.symm , } ,
        rw eq_Ioi , } ,
    } ,
    rw eq ,
    have mble_indic_P : measurable (indic P) := (indic_mble_iff P).mpr P_mble ,
    have mble_indic_Pc : measurable (indic Pᶜ) := (indic_mble_iff Pᶜ).mpr (measurable_set.compl P_mble) ,
    have mble_term₁ : measurable ((indic P) * f₁) := measurable.mul mble_indic_P key ,
    have mble_term₂ : measurable ((indic Pᶜ) * cfun) := measurable.mul mble_indic_Pc (measurable_const) ,
    exact measurable.add mble_term₁ mble_term₂ , } ,
  rw [rwkey, rwkeyseq] ,
  exact portmanteau_open_fatou (volume.restrict {t : ℝ | 0 < t} : measure ℝ) preim_open μseq μseq_fin μ μ_fin mble_meas hopcond ,
end


lemma portmanteau_open_imp_cont
  (μseq : ℕ → @measure_theory.measure α (borel α)) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : @measure_theory.measure α (borel α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
    portmanteau_open μseq μ → portmanteau_continuous_ennval μseq μ :=
begin
  intros hopcond f f_cont f_bdd ,
  suffices : limsup_enn ( λ (n : ℕ) , @lintegral α (borel(α)) (μseq(n)) f ) ≤ @lintegral α (borel(α)) μ f ,
  { have liminf_ge := portmanteau_open_imp_cont_liminf μseq μseq_fin μ μ_fin hopcond f f_cont f_bdd ,
    exact tendsto_of_le_liminf_of_limsup_le liminf_ge this , } ,
  cases f_bdd with c hc ,
  have ne_top : (c : ennreal) ≠ ⊤ := coe_ne_top ,
  set g := (( λ (a : α) , (c : ennreal)) - f) with hg ,
  have g_cont : continuous g ,
  { set φ := (λ (x : ennreal) , (c:ennreal) - x) with hφ ,
    have cts : continuous φ := continuous_const_sub_ennreal _ ne_top ,
    have g_eq : g = φ ∘ f := by refl ,
    apply continuous.comp cts f_cont , } ,
  have g_bdd : bdd_ennval g ,
  { use c ,
    intros a,
    rw hg ,
    exact ennreal.sub_le_self c (f(a)) , } ,
  have key := portmanteau_open_imp_cont_liminf μseq μseq_fin μ μ_fin hopcond g g_cont g_bdd ,
  rw hg at key ,
  have eq := lintegral_cst_sub μ ne_top f (continuous.borel_measurable f_cont) hc ,
  have eq_seq' := λ n , lintegral_cst_sub (μseq(n)) ne_top f (continuous.borel_measurable f_cont) hc ,
  have eq_seq : (λ n , @lintegral α (borel(α)) (μseq(n)) g) = (λ n , (c:ennreal) - @lintegral α (borel(α)) (μseq(n)) f)
    := funext eq_seq' ,
  rw [eq , eq_seq , liminf_enn_rw] at key ,
  rw (liminf_const_sub c ne_top (λ n , @lintegral α (borel(α)) (μseq(n)) f)) at key ,
  have le₁ : @lintegral α (borel(α)) μ f ≤ c ,
  { have le := @lintegral_mono α (borel(α)) μ f _ hc ,
    rwa lintegral_cst μ c at le , } ,
  have le₂ : limsup_enn (λ n , @lintegral α (borel(α)) (μseq(n)) f) ≤ c ,
  { suffices : ∀ n , @lintegral α (borel(α)) (μseq(n)) f ≤ c ,
    { exact limsup_le_of_le_ennreal this , } ,
    intros n ,
    have le := @lintegral_mono α (borel(α)) (μseq(n)) f _ hc ,
    rwa lintegral_cst (μseq(n)) c at le , } ,
  exact le_of_self_sub_le_self_sub_ennreal c _ _ ne_top le₁ le₂ key ,
end



end portmanteau_open_implies_continuous

end portmanteau

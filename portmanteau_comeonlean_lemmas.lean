/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.integration
import topology.metric_space.basic
import topology.instances.real
import topology.instances.ennreal
import topology.instances.nnreal
import topology.algebra.infinite_sum
import portmanteau_definitions



noncomputable theory
open set 
open filter
open order
open_locale topological_space ennreal big_operators


namespace portmanteau



section portmanteau_comeonlean_lemmas



/-
abbreviation lim_R (s : ℕ → ℝ) (l : ℝ) : Prop := tendsto s at_top (𝓝 l)

abbreviation lim_enn (s : ℕ → ennreal) (l : ennreal) : Prop := tendsto s at_top (𝓝 l)

lemma lim_R_rw (s : ℕ → ℝ) (l : ℝ) : lim_R s l = tendsto s at_top (𝓝 l) := by refl
-/


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


lemma ennreal_eq_top_of_forall_nnreal_ge (z : ennreal) : (∀ (x : nnreal) , ennreal.of_real x ≤ z) → z = ⊤ :=
begin
  contrapose ,
  intros hz ,
  push_neg ,
  have key := ennreal.lt_iff_exists_nnreal_btwn.mp (lt_top_iff_ne_top.mpr hz) ,
  cases key with x hx ,
  use x ,
  simp only [hx.1, ennreal.of_real_coe_nnreal] ,
end


lemma ennreal_eq_top_of_forall_real_ge (z : ennreal) : (∀ (x : ℝ) , ennreal.of_real x ≤ z) → z = ⊤ :=
begin
  intros h ,
  apply ennreal_eq_top_of_forall_nnreal_ge ,
  intros x' ,
  exact h x' ,
end


lemma ennreal_eq_top_of_forall_nat_ge (z : ennreal) : (∀ (n : ℕ) , coe n ≤ z) → z = ⊤ :=
begin
  intro h,
  suffices : (∀ (x : nnreal) , ennreal.of_real x ≤ z) ,
  { exact ennreal_eq_top_of_forall_nnreal_ge z this , } ,
  intros x ,
  have ex : ∃ (n : ℕ) , x ≤ n := exists_nat_ge x ,
  cases ex with n hn ,
  apply le_trans (ennreal.of_real_le_of_real hn) ,
  simp only [h n, nnreal.coe_nat_cast, ennreal.of_real_coe_nat] ,
end


lemma sum_infinitely_many_ones_ennreal : ∑' (i : ℕ), (1:ennreal) = ⊤ :=
begin
  apply ennreal_eq_top_of_forall_nat_ge ,
  intros n ,
  have ones_summable : summable (λ (n : ℕ) , (1:ennreal)) := ennreal.summable ,
  have key := sum_le_tsum (finset.range n) (by tidy) ones_summable ,
  have eq : ∑ i in (finset.range n) , (1 : ennreal) = n ,
  { simp only [finset.sum_const, finset.card_range, nat.smul_one_eq_coe] , } ,
  rwa eq at key ,
end


lemma sum_infinitely_many_pos_const_ennreal' (a : nnreal) (a_pos : 0 < a) : ∑' (i : ℕ), (a:ennreal) = ⊤ :=
begin
  apply ennreal_eq_top_of_forall_nnreal_ge ,
  intros b ,
  have ex' : ∃ (n : ℕ) , b/a ≤ n := exists_nat_ge _ ,
  have ex : ∃ (n : ℕ) , b ≤ n * a ,
  { cases ex' with m hm ,
    use m ,
    have key := mul_le_mul_right' hm a ,
    have cancancel : b / a * a = b , -- Hide in a corner.
    { rw [div_mul_eq_mul_div a b a , mul_comm , mul_div_right_comm a b a , div_self (ne_of_gt a_pos)] ,
      exact one_mul _ , } ,
    rwa cancancel at key , } ,
  cases ex with n hn ,
  have hn' := ennreal.coe_mono hn ,
  have eq₀ : ((a * n : nnreal) : ennreal) = (a : ennreal)*( n: ennreal) := by simp only [ennreal.coe_nat, ennreal.coe_mul],
  nth_rewrite 1 mul_comm at eq₀ ,
  have eq : ∑ i in (finset.range n) , (a : ennreal) = n * a ,
  { simp only [finset.sum_const, nsmul_eq_mul, finset.card_range] , } ,
  rw ← eq at eq₀ ,
  rw mul_comm at eq₀ , -- Hide in another corner.
  rw eq₀ at hn' ,
  have const_summable : summable (λ (n : ℕ) , (a:ennreal)) := ennreal.summable ,
  have key := sum_le_tsum (finset.range n) (by tidy) const_summable ,
  have eq₁ : ennreal.of_real b = (b:ennreal) := ennreal.of_real_coe_nnreal ,
  rw eq₁ ,
  exact le_trans hn' key ,
end


lemma sum_infinitely_many_pos_const_ennreal (a : ennreal) (a_pos : 0 < a) : ∑' (i : ℕ), (a:ennreal) = ⊤ :=
begin
  by_cases a_top : a = ⊤ ,
  { rw a_top ,
    exact ennreal.tsum_top , } ,
  { have eq : ( a.to_nnreal : ennreal) = a := ennreal.coe_to_nnreal a_top ,
    have a_pos' : 0 < a.to_nnreal := with_top.coe_lt_iff.mp a_pos (ennreal.to_nnreal a) (eq.symm) ,
    have key := sum_infinitely_many_pos_const_ennreal' a.to_nnreal a_pos' ,
    rwa eq at key , } ,
end


lemma add_le_add_ennreal {a₁ b₁ a₂ b₂ : ennreal} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
  a₁ + b₁ ≤ a₂ + b₂ := add_le_add ha hb 


lemma le_self_add_ennreal (a b : ennreal) : a ≤ a + b :=
begin
  suffices : a + 0 ≤ a + b ,
  { simpa [this] , } ,
  apply add_le_add_ennreal _ _ ,
  { have a_eq_a : a = a := by refl ,
    exact le_of_eq a_eq_a , } ,
  simp only [zero_le, ennreal.bot_eq_zero] ,
end


lemma self_sub_le_self_sub_ennreal (a b₁ b₂ : ennreal) (hb : b₂ ≤ b₁) : a - b₁ ≤ a - b₂ :=
begin
  have a_eq_a : a = a := by refl ,
  apply ennreal.sub_le_sub (le_of_eq a_eq_a) hb ,
end


lemma le_of_self_sub_le_self_sub_ennreal (a b₁ b₂ : ennreal) (a_ne_top : a ≠ ⊤) (hb₁ : b₁ ≤ a) (hb₂ : b₂ ≤ a)
  (hb : a - b₁ ≤ a - b₂) : b₂ ≤ b₁ :=
begin
  have eq₁ : a - (a-b₁) = b₁ := ennreal.sub_sub_cancel (lt_top_iff_ne_top.mpr a_ne_top) hb₁ ,
  have eq₂ : a - (a-b₂) = b₂ := ennreal.sub_sub_cancel (lt_top_iff_ne_top.mpr a_ne_top) hb₂ ,
  rw [← eq₁ , ← eq₂] ,
  apply self_sub_le_self_sub_ennreal a (a-b₂) (a-b₁) hb ,
end


lemma sub_larger_ennreal (a b : ennreal) (hab : a ≤ b) : a - b = 0 :=
begin
  exact ennreal.sub_eq_zero_iff_le.mpr hab ,
end


lemma fin_pos_nnreal_of_fin_pos_ennreal 
  (ε : ennreal) (ε_pos : 0 < ε) (ε_fin : ε ≠ ⊤) :
    0 < ε.to_nnreal :=
begin
  set ε' := ε.to_nnreal with hε' ,
  have eq : ennreal.of_nnreal_hom ε' = ε := ennreal.coe_to_nnreal ε_fin ,
  by_contra contra ,
  simp only [not_lt, le_zero_iff] at contra ,
  rw contra at eq ,
  simp only [ennreal.coe_of_nnreal_hom, ennreal.coe_zero] at eq,
  rw ←eq at ε_pos ,
  have key := ne_of_lt ε_pos ,
  contradiction ,
end


lemma ennreal_lt_top_iff_ne_top (z : ennreal) : 
  z < ⊤ ↔ z ≠ ⊤ 
    := lt_top_iff_ne_top


lemma ennreal_lt_top_of_ne_top (z : ennreal) (hz : z < ⊤) : z ≠ ⊤ 
    := (ennreal_lt_top_iff_ne_top z).mp hz


lemma ennreal_ne_top_of_lt_top (z : ennreal) (hz : z ≠ ⊤) : z < ⊤
    := (ennreal_lt_top_iff_ne_top z).mpr hz


lemma lt_add_pos_ennreal (z ε : ennreal) (hz : z ≠ ⊤) (ε_pos : 0 < ε) : 
  z < z + ε :=
begin
  by_cases ε_fin : ε = ⊤ ,
  { simp only [ε_fin, ennreal.add_top] ,
    exact lt_top_iff_ne_top.mpr hz , } ,
  have key := ((@ennreal.add_lt_add_iff_left z) ε 0 ( (ennreal_lt_top_iff_ne_top z).mpr hz)).mpr ε_pos,
  simp only [add_zero] at key ,
  exact key ,
end


lemma nbhd_top_ennreal' (U : set ennreal) (hU : U ∈ 𝓝 ∞) :
  ∃ (a : nnreal) , Ioi (a : ℝ≥0∞) ⊆ U :=
begin
  have ns := ennreal.nhds_top' ,
  rw ns at hU ,
  rw mem_infi_iff' at hU ,
  rcases hU with ⟨ I , ⟨ I_fin , ⟨v , ⟨ V_supset_Ioi , inter_V_subset_U ⟩ ⟩ ⟩ ⟩ ,
  have ex_ub : ∃ (b : nnreal) , ∀ i ∈ I , i ≤ b 
    := exists_upper_bound_image I (λ (b : nnreal), b) I_fin , -- don't go to plain sight!
  cases ex_ub with b hb ,
  use b ,
  intros x hx ,
  rw mem_Ioi at hx,
  have key : x ∈ ⋂ (i ∈ I) , (v i) ,
  { rw mem_bInter_iff ,
    intros i hi ,
    have key := V_supset_Ioi i hi ,
    rw mem_principal_sets at key ,
    exact key (lt_of_le_of_lt (ennreal.coe_mono (hb i hi)) hx) , } ,
  exact inter_V_subset_U key ,
end


lemma nbhd_top_ennreal (U : set ennreal) (hU : U ∈ 𝓝 ∞) :
  ∃ (a < ⊤) , Ioi (a : ℝ≥0∞) ⊆ U :=
begin
  have key := nbhd_top_ennreal' U hU ,
  cases key with a' ha' ,
  use a' ,
  exact ⟨ ennreal.coe_lt_top , ha' ⟩ ,
end


lemma continuous_const_sub_nnreal (a : nnreal) :
  continuous (λ (x : nnreal) , a-x ) :=
begin
  set sub := (λ (p : nnreal × nnreal) , p.1 - p.2) with h_sub ,
  set to_pair := (λ (x : nnreal) , (⟨a,x⟩ : nnreal × nnreal)) with h_to_pair ,
  have cont_to_pair : continuous to_pair 
    := @continuous.prod_mk nnreal nnreal nnreal _ _ _ (λ x , a) (λ x , x) (continuous_const) (continuous_id') ,
  have eq : sub ∘ to_pair = (λ (x : nnreal) , a-x ) := by refl , -- hide in corners
  rw ← eq ,
  exact continuous.comp continuous_sub cont_to_pair ,
end

-- Why could I not find (a symmetric version of) this?
lemma equality_of_restrictions {γ δ : Type*} [topological_space γ] {f g : γ → δ} {G : set γ} {x₀ : γ} (hfg : ∀ (x ∈ G) , f x = g x) (hx₀ : x₀ ∈ G) :
  map f (𝓝[G] x₀) ≤ map g (𝓝[G] x₀) :=
begin
  intros V hV ,
  rcases hV with ⟨ U , hU_nhd , ⟨ T , ⟨ hT_princ , hUT ⟩ ⟩  ⟩ ,
  use U ,
  split , 
  { exact hU_nhd , } ,
  use G ,
  split , 
  { exact mem_principal_self G , } ,
  intros y hy ,
  have y_in_G : y ∈ G := mem_of_mem_inter_right hy ,
  rw mem_preimage ,
  rw (hfg y (mem_of_mem_inter_right hy)) ,
  have y_in_bigger : y ∈ U ∩ T := inter_subset_inter_right U hT_princ hy , 
  exact hUT y_in_bigger , 
end


lemma sub_ennreal_nnreal_continuous_on_ne_top : 
  continuous_on (λ p : ennreal × nnreal, p.1 - p.2) { p : ennreal × nnreal | p.1 ≠ ⊤ } :=
begin
  set proj : ennreal × nnreal → nnreal × nnreal := λ p , ⟨ennreal.to_nnreal(p.1), p.2⟩ with h_proj ,
  have proj_cont : continuous_on proj { p : ennreal × nnreal | p.1 ≠ ⊤ } ,
  { have id_cont : continuous_on (λ (z : nnreal) , z) univ := continuous_on_id ,
    have eq_fun : proj = prod.map ennreal.to_nnreal (λ (z : nnreal) , z) := by refl ,
    have eq_set : { p : ennreal × nnreal | p.1 ≠ ⊤ } = { z : ennreal | z ≠ ⊤ }.prod (univ : set nnreal) := by tidy ,
    rw [eq_fun, eq_set] ,
    exact continuous_on.prod_map ennreal.continuous_on_to_nnreal id_cont , } ,
  set sub := (λ p : nnreal × nnreal, p.1 - p.2) with h_sub ,
  have eq : ∀ p ∈ { p : ennreal × nnreal | p.1 ≠ ⊤ } , (λ p : ennreal × nnreal, p.1 - p.2) p = (coe ∘ sub ∘ proj) p ,
  { intros p hp ,
    rw [h_proj , h_sub] ,
    dsimp ,
    simp only [mem_set_of_eq, ne.def] at hp ,
    have coes : p.fst = (p.fst.to_nnreal : ennreal) ,
    { simp only [hp, ne.def, not_false_iff, ennreal.coe_to_nnreal] , } ,
    nth_rewrite 0 coes ,
    apply ennreal.coe_sub.symm , } ,
  suffices : continuous_on (coe ∘ sub ∘ proj) { p : ennreal × nnreal | p.1 ≠ ⊤ } ,
  { exact (continuous_on_congr (eq_on.symm eq)).mp this , } ,
  have cont := continuous.comp_continuous_on continuous_sub proj_cont ,
  apply continuous.comp_continuous_on (ennreal.continuous_coe) cont ,
end


lemma sub_sum_nnreal (a b c : nnreal) : a - (b + c) = a - b - c :=
begin
  have lhs : a - (b + c) = (a.val - b.val - c.val).to_nnreal , --nnreal.of_real (a.val - b.val - c.val) ,
  { rw nnreal.sub_def ,
    apply congr_arg ,
    cases c, 
    cases b, 
    cases a, 
    dsimp at * ,
    ring , } ,
  have rhs : a - b - c = (a.val - b.val - c.val).to_nnreal , -- nnreal.of_real (a.val - b.val - c.val) ,
  { by_cases hab : b ≤ a ,
    { have hab' : b.val ≤ a.val := hab ,
      have hab'' : 0 ≤ a.val - b.val := by linarith ,
      have a_sub_b_val : (a-b).val = a.val - b.val ,
      { have mx : max (a.val - b.val) 0 = a.val - b.val := max_eq_left hab'' ,
        rw nnreal.sub_def ,
        unfold real.to_nnreal ,
        simp_rw mx ,
        exact mx , } ,
      set d := a-b with hd ,
      rw ←a_sub_b_val ,
      rw nnreal.sub_def ,
      apply congr_arg ,
      refl , } ,
    { simp only [not_le] at hab ,
      have le : a ≤ b := le_of_lt hab , -- Such reasoning,
      have le' : a.val ≤ b.val := le , -- obviously, is the 
      have le'' : a.val - b.val ≤ 0 := by linarith , -- very
      have c_nn : 0 ≤ c.val := c.prop , -- heart of the asserted
      have le''' : a.val - b.val - c.val ≤ 0 := by linarith , -- fact.
      have mx : max (a.val - b.val - c.val) 0 = 0 := max_eq_right le''' ,
      have a_sub_b : a - b = 0 := nnreal.sub_eq_zero le ,
      have z_sub_c : 0 - c = 0 := le_zero_iff.mp (nnreal.sub_le_self) ,
      rw [a_sub_b , z_sub_c] ,
      unfold real.to_nnreal ,
      simp_rw mx ,
      refl , } ,
  } ,
  rw [lhs, rhs] ,
end


lemma sub_sum_ennreal (a b c : ennreal) : a - (b + c) = a - b - c :=
begin
  by_cases fin : b < ∞ ∧ c < ∞ ,
  { have b_eq : (b.to_nnreal : ennreal) = b := ennreal.coe_to_nnreal (ennreal.lt_top_iff_ne_top.mp fin.left) ,
    have c_eq : (c.to_nnreal : ennreal) = c := ennreal.coe_to_nnreal (ennreal.lt_top_iff_ne_top.mp fin.right) ,
    rw [←b_eq, ←c_eq] ,
    set ι := (coe : nnreal → ennreal) with hι ,
    set b' := b.to_nnreal with hb' ,
    set c' := c.to_nnreal with hc' ,
    have eq₂ : ι (b'+c') = ι b' + ι c' := @ennreal.coe_add b' c' ,
    have sum_fin : b + c < ⊤ 
      := by simp only [fin.left, fin.right, ennreal.add_lt_top, and_self] ,
    by_cases a_top : a = ⊤ ,
    { rw a_top ,
      have sum_ne_top := ennreal.lt_top_iff_ne_top.mp sum_fin ,
      have lhs : ⊤ - ι (b'+c') = ⊤ := ennreal.top_sub_coe , -- to a corner
      have rhs₁ : ⊤-(ι b') = ⊤ := ennreal.top_sub_coe , 
      have rhs₂ : ⊤-(ι c') = ⊤ := ennreal.top_sub_coe ,
      rw [rhs₁ , rhs₂ , ←eq₂ , lhs] , } ,
    { have a_eq : (a.to_nnreal : ennreal) = a := ennreal.coe_to_nnreal a_top ,
      rw [←a_eq] ,
      set a' := a.to_nnreal with ha' ,
      have key := sub_sum_nnreal a.to_nnreal b.to_nnreal c.to_nnreal ,
      have key' := congr_arg (coe : nnreal → ennreal) key , -- quickly, to another corner
      have eq₁ : ι (a' - (b'+c')) = (ι a') - (ι (b'+c')) := @ennreal.coe_sub (b'+c') a' ,
      have eq₃ : ι (a' - b' - c') = (ι (a' - b')) - (ι (c')) := @ennreal.coe_sub c' (a'-b') ,
      have eq₄ : ι (a' - b') = (ι a') - (ι b') := @ennreal.coe_sub b' a' ,
      rwa [←eq₂, ←eq₄, ←eq₁, ←eq₃] , } ,
  } ,
  { rw not_and_distrib at fin , -- hide
    cases fin with not_fin not_fin ; simp only [not_lt, top_le_iff] at not_fin ,
    { rw [not_fin , ennreal.top_add] ,
      simp only [ennreal.sub_infty, ennreal.zero_sub] , } ,
    { rw [not_fin , ennreal.add_top] ,
      simp only [ennreal.sub_infty, ennreal.zero_sub] , } ,
  } ,
end


lemma continuous_sub_ennreal_nnreal : 
  continuous (λ p : ennreal × nnreal, p.1 - p.2) :=
begin
  apply continuous_iff_continuous_at.mpr ,
  intros p ,
  by_cases fst_top : p.fst = ⊤ ,
  { intros V hV ,
    simp_rw fst_top at hV ,
    simp only [ennreal.top_sub_coe] at hV ,
    have V_super := nbhd_top_ennreal' V hV ,
    cases V_super with v hv ,
    set U := set.prod (Ioi (p.2 + v + 1 : ennreal)) (Iio (p.2 + 1)) with hU ,
    have lt₁ : (⊤ : ℝ≥0∞) ∈ (Ioi (p.2 + v + 1 : ennreal)) ,
    { simp only [true_and, ennreal.coe_lt_top, mem_Ioi, ennreal.add_lt_top] ,
      exact dec_trivial , } ,
    have nbhd₁ : Ioi (p.2+v+1 : ennreal) ∈ 𝓝 p.1,
    { rw fst_top ,
      --exact is_open.mem_nhds (is_open_Ioi) lt₁ ,
      exact Ioi_mem_nhds lt₁ , } ,
    have nbhd₂ : Iio (p.2+1) ∈ 𝓝 p.2 := is_open.mem_nhds (is_open_Iio) (by simp only [mem_Iio, lt_add_iff_pos_right, zero_lt_one]) ,
      --:= mem_nhds_sets (is_open_Iio) (by simp only [mem_Iio, lt_add_iff_pos_right, zero_lt_one]) ,
    have nbhd := prod_is_open.mem_nhds nbhd₁ nbhd₂ ,
      --: set.prod (Ioi (p.2 + v + 1 : ennreal)) (Iio (p.2 + 1)) ∈ 𝓝 p
      --:= by sorry , -- the above works in another version of mathlib
    rw [←hU , prod.mk.eta] at nbhd , --works in another version of mathlib
    --have nbhd : U ∈ 𝓝 p := by sorry , -- again, use the above in a fresh mathlib
    set f := (λ p : ennreal × nnreal, p.1 - p.2) with hf ,
    have ss : U ⊆ f⁻¹' V ,
    { rintros q ⟨ hq₁ , hq₂⟩ ,
      simp only [mem_Ioi] at hq₁ ,
      simp only [mem_Iio] at hq₂ ,
      have hq₂' : (q.snd : ennreal) < p.snd + 1 := ennreal.coe_lt_coe.mpr hq₂ ,
      have hq₁' : (p.snd : ennreal) + 1 < q.fst - v ,
      { have le : (v : ennreal) ≤ q.fst ,
        { apply le_of_lt _ ,
          calc (v : ennreal) ≤ (v : ennreal) + (1 + p.snd) : le_self_add_ennreal _ _
          ... = (p.snd : ennreal) + v + 1                  : by ring
          ... < q.fst                                      : hq₁ , } ,
        have eq : q.fst - v + v = q.fst := ennreal.sub_add_cancel_of_le le ,
        have eq' : (p.snd : ennreal) + 1 + v = (p.snd : ennreal) + v + 1 := by ring ,
        rw [←eq , ←eq'] at hq₁ ,
        exact (ennreal.add_lt_add_iff_right (@ennreal.coe_lt_top v)).mp hq₁ , } ,
      have gt : (v : ennreal) < f q ,
      { rw hf ,
        dsimp ,
        have lt := lt_trans hq₂' hq₁' ,
        have lt' := ennreal.zero_lt_sub_iff_lt.mpr lt ,
        have rw₀ : q.fst - v - q.snd = q.fst - q.snd - v ,
        { rw [←(sub_sum_ennreal _ _ _) , ←(sub_sum_ennreal _ _ _) , add_comm ] , } ,
        rw rw₀ at lt' ,
        apply ennreal.zero_lt_sub_iff_lt.mp lt' ,
      } ,
      exact hv gt , } ,
    apply (𝓝 p).sets_of_superset nbhd ss , } ,
  { intros V hV ,
    dsimp at hV ,
    have key := sub_ennreal_nnreal_continuous_on_ne_top p fst_top hV ,
    rcases key with ⟨ U , U_nbhd , ⟨ T , ⟨ hT , hUT ⟩ ⟩ ⟩ ,
    set S := { p : ennreal × nnreal | p.1 ≠ ⊤ } with hS ,
    rw mem_principal_sets at hT ,
    have S_prod : S = {z : ennreal | z ≠ ⊤}.prod (univ : set nnreal) ,
    { ext q ,
      simp only [and_true, mem_univ, mem_set_of_eq, mem_prod] , } ,
    have nbhd₁ : {z : ennreal | z ≠ ⊤} ∈ 𝓝 p.fst := is_open.mem_nhds (is_open_ne) (fst_top) , -- mem_nhds_sets (is_open_ne) (fst_top) ,
    have nbhd₂ : (univ : set nnreal) ∈ 𝓝 p.snd := is_open.mem_nhds (is_open_univ) (mem_univ _) ,
    have S_nbhd : {z : ennreal | z ≠ ⊤}.prod (univ : set nnreal) ∈ 𝓝 (⟨p.1, p.2⟩ : ennreal × nnreal) 
      := prod_is_open.mem_nhds nbhd₁ nbhd₂ , -- prod_mem_nhds_sets nbhd₁ nbhd₂ ,
    rw [←S_prod , prod.mk.eta] at S_nbhd ,
    have US_nbhd : U ∩ S ∈ 𝓝 p := (𝓝 p).inter_sets U_nbhd S_nbhd ,
    have US_ss_UT : U ∩ S ⊆ U ∩ T := inter_subset_inter_right U hT ,
    have UT_nbhd : U ∩ T ∈ 𝓝 p := (𝓝 p).sets_of_superset US_nbhd US_ss_UT ,
    apply (𝓝 p).sets_of_superset UT_nbhd hUT , } ,
end


-- Remark: 
-- This is not even the right generality for the continuity of
-- subtraction on a subset of `ennreal × ennreal`. I guess we
-- have continuity on the complement of the singleton `{⟨∞,∞⟩}`.
-- With that, a few of the subsequent corner-hidings would simplify.
-- But I had surprisingly hard time working with ennreals and 
-- subtraction, so I gave up and just aimed at a sorry-free (TM)
-- exercise...
lemma continuous_sub_ennreal_ennreal_snd_ne_top : 
  continuous_on (λ p : ennreal × ennreal, p.1 - p.2) { p : ennreal × ennreal | p.snd ≠ ∞} :=
begin
  have g_cont := continuous_sub_ennreal_nnreal ,
  set g := (λ p : ennreal × nnreal, p.1 - p.2) with hg ,
  set f := (λ p : ennreal × ennreal, p.1 - p.2) with hf ,
  set φ := (λ p : ennreal × ennreal, ( ⟨p.1 , (p.2).to_nnreal ⟩ : ennreal × nnreal ) ) with hφ ,
  set S := { p : ennreal × ennreal | p.snd ≠ ∞} with hS ,
  have φ_cont : continuous_on φ S ,
  { have key₁' : continuous (λ (z : ennreal) , z ) := continuous_id' ,
    have key₁ : continuous_on (λ (z : ennreal) , z ) univ := continuous.continuous_on key₁' ,
    have key₂ := ennreal.continuous_on_to_nnreal ,
    have φ_prod_map : φ = prod.map (λ (z : ennreal) , z ) ennreal.to_nnreal := by refl ,
    have S_prod_set : S = (univ : set ennreal).prod {w : ennreal | w ≠ ∞}, 
    { simp only [eq_self_iff_true] at hS , 
      ext p, 
      cases p, 
      dsimp , 
      simp only [true_and, mem_univ] , } ,
    rw [φ_prod_map , S_prod_set] ,
    exact continuous_on.prod_map key₁ key₂ , } ,
  have comp_cont : continuous_on (g ∘ φ) S := continuous.comp_continuous_on g_cont φ_cont ,
  have agree : ∀ p ∈ S , f p = (g ∘ φ) p ,
  { intros p hpS ,
    rw [hf , hg , hφ ] ,
    simp only [function.comp_app] ,
    rw ennreal.coe_to_nnreal hpS , } ,
  have pfun_eq : pfun.res f S = pfun.res (g ∘ φ) S ,
  { ext ,
    rw pfun.mem_res ,
    rw pfun.mem_res ,
    split ,
    { rintros ⟨ hx , val ⟩ ,
      rw agree x hx at val ,
      exact ⟨ hx , val ⟩ , } ,
    { rintros ⟨ hx , val ⟩ ,
      rw ← agree x hx at val ,
      exact ⟨ hx , val ⟩ , } ,
  } ,
  intros p hp ,
  rw continuous_within_at_iff_ptendsto_res ,
  rw [pfun_eq , agree p hp] ,
  rw ← continuous_within_at_iff_ptendsto_res ,
  exact comp_cont p hp ,
end


-- Remark: This should get an easier proof from the right
-- continuity result of subtraction on ennreals.
lemma continuous_on_const_sub_ennreal (a : ennreal) (a_ne_top : a ≠ ⊤) :
  continuous_on (λ (x : ennreal) , a-x ) {z : ennreal | z ≠ ⊤} :=
begin
  set f := (λ (x : ennreal) , a-x ) with hf ,
  set S := { z : ennreal | z ≠ ⊤ } with hS ,
  have cont_cast : continuous_on ennreal.to_nnreal S := ennreal.continuous_on_to_nnreal ,
  set f₀ := (λ (x : nnreal) , a.to_nnreal-x ) with hf₀ ,
  have cont_f₀ : continuous f₀ := continuous_const_sub_nnreal (ennreal.to_nnreal a) ,
  have cont_f₀' : continuous_on f₀ univ := continuous.continuous_on cont_f₀ ,
  have cont_comp' := continuous_on.comp cont_f₀' cont_cast (by simp only [preimage_univ, subset_univ]) ,
  have cont_comp := continuous.comp_continuous_on ennreal.continuous_coe cont_comp' ,
  have eq₀ : ( ∀ (z ∈ S) , f z = (coe ∘ f₀ ∘ ennreal.to_nnreal) z ) ,
  { intros z hz ,
    rw [hf , hf₀] ,
    dsimp ,
    have a_eq := ennreal.coe_to_nnreal a_ne_top ,
    have z_eq := ennreal.coe_to_nnreal hz ,
    rw [←a_eq , ←z_eq] ,
    apply ennreal.coe_sub.symm , } ,
  intros z hzS V hV ,
  have hV' := hV ,
  rw (eq₀ z hzS) at hV' ,
  specialize cont_comp z hzS hV' ,
  have key := equality_of_restrictions eq₀ hzS ,
  exact key cont_comp ,
end


-- Remark: This also should get an easier proof from the right
-- continuity result of subtraction on ennreals.
lemma continuous_const_sub_ennreal (a : ennreal) (a_ne_top : a ≠ ⊤) :
  continuous (λ (x : ennreal) , a-x ) :=
begin
  set f := (λ (x : ennreal) , a-x ) with hf ,
  apply continuous_iff_continuous_at.mpr ,
  intros x ,
  by_cases hx : x = ⊤ ,
  { rw hx ,
    have mem_Ioi : ⊤ ∈ Ioi a := ennreal.lt_top_iff_ne_top.mpr a_ne_top ,
    have open_Ioi : is_open (Ioi a) := is_open_Ioi , 
    have nhd_Ioi : Ioi a ∈ 𝓝 ⊤ := is_open.mem_nhds open_Ioi mem_Ioi , --mem_nhds_sets open_Ioi mem_Ioi ,
    intros V hV ,
    have val_at_top : f ⊤ = 0 := by simp only [ennreal.sub_eq_zero_iff_le, le_top] ,
    rw val_at_top at hV ,
    have mem_V : (0 : ennreal) ∈ V ,
    { exact mem_of_mem_nhds hV , } ,
    have ss_preim : Ioi a ⊆ f⁻¹' V ,
    { intros z hz ,
      have val : f z = 0 := ennreal.sub_eq_zero_iff_le.mpr (le_of_lt hz) ,
      rwa ← val at mem_V , } ,
    exact (𝓝 ⊤).sets_of_superset nhd_Ioi ss_preim , } ,
  { set S := { z : ennreal | z ≠ ⊤ } with hS ,
    have nbhd : S ∈ (𝓝 x) ,
    { have opn : is_open S := is_open_ne ,
      --exact mem_nhds_sets opn good ,
      exact is_open.mem_nhds opn hx , } ,
    suffices : continuous_on f S ,
    { intros V hV ,
      have key := this x hx hV ,
      rcases key with ⟨ U , U_nhd , ⟨ T , hT , hUT⟩ ⟩ ,
      rw mem_principal_sets at hT ,
      have T_nbhd : T ∈ (𝓝 x) := (𝓝 x).sets_of_superset nbhd hT ,
      have nbhd₀ : U ∩ T ∈ (𝓝 x) := inter_mem_sets U_nhd T_nbhd ,
      rw mem_map ,      
      apply (𝓝 x).sets_of_superset nbhd₀ hUT , } ,
    exact continuous_on_const_sub_ennreal a a_ne_top , } ,
end


lemma lim_enn_of_lim_R {s : ℕ → ℝ} {l : ℝ} (hlim : tendsto s at_top (𝓝 l)) : 
  tendsto (ennreal.of_real ∘ s) at_top (𝓝 (ennreal.of_real l))
    := ennreal.tendsto_of_real hlim 


lemma nnreal_nbhd_finite_ennreal (x : ennreal) :
  x ≠ ⊤ → { z : ennreal | z ≠ ⊤ } ∈ 𝓝 x :=
begin
  intros hx ,
  have op : is_open { z : ennreal | z ≠ ⊤ } := is_open_ne ,
  --TODO: depending on mathlib version, one of the following works...
  --exact mem_nhds_sets op hx ,
  exact is_open.mem_nhds op hx ,
end


lemma ennreal_to_nnreal_continuous_on_nnreal :
  continuous_on ennreal.to_nnreal { z : ennreal | z ≠ ⊤ } :=
begin
  exact ennreal.continuous_on_to_nnreal , 
end


lemma ennreal_to_real_continuous_on_nnreal :
  continuous_on ennreal.to_real { z : ennreal | z ≠ ⊤ } :=
begin
  have eq : ennreal.to_real = nnreal.to_real_hom ∘ ennreal.to_nnreal := by refl ,
  rw eq ,
  intros z hz ,
  have cont_at_nnreal 
    := continuous_on.continuous_at ennreal.continuous_on_to_nnreal (nnreal_nbhd_finite_ennreal z hz), 
  apply @tendsto.comp _ _ _ _ _ _ (𝓝 (ennreal.to_nnreal z)) _ ,
  { simp only [nnreal.coe_to_real_hom, nnreal.tendsto_coe] ,
    intros U hU ,
    assumption , } ,
  { exact tendsto_inf_left cont_at_nnreal , } ,
end


lemma ennreal_ne_top_of_le_nnreal {c : nnreal} {x : ennreal} (h_le : x ≤ c) : x ≠ ⊤ :=
begin
  by_contra contra ,
  rw not_not at contra ,
  rw contra at h_le ,
  simp only [ennreal.not_top_le_coe] at h_le ,
  exact h_le , 
end


lemma finval_of_bdd_ennval {α : Type*} {f : α → ennreal} :
  bdd_ennval f → ∀ (a : α) , f(a) ≠ ⊤ :=
begin
  intros f_bdd a ,
  cases f_bdd with c hc ,
  exact ennreal_ne_top_of_le_nnreal (hc a) ,
end


lemma bdd_Rval_add {α : Type*} {f g : α → ℝ}
  (f_bdd : bdd_Rval f) (g_bdd : bdd_Rval g) : bdd_Rval (f+g) :=
begin
  cases f_bdd with c hc ,
  cases g_bdd with d hd ,
  use (c+d) ,
  intros x ,
  apply le_trans (abs_add (f(x)) (g(x))) (add_le_add (hc x) (hd x)) ,
end


lemma bdd_ennval_add {α : Type*} {f g : α → ennreal}
  (f_bdd : bdd_ennval f) (g_bdd : bdd_ennval g) : bdd_ennval (f+g) :=
begin
  cases f_bdd with c hc ,
  cases g_bdd with d hd ,
  use (c+d) ,
  intros x ,
  exact add_le_add (hc x) (hd x) ,
end


lemma bdd_ennval_of_le_bdd_ennval {α : Type*} {f g : α → ennreal}
  (hfg : f ≤ g) (g_bdd : bdd_ennval g) : bdd_ennval f :=
begin
  cases g_bdd with c hc ,
  use c ,
  intros x ,
  exact le_trans (hfg x) (hc x) ,
end


lemma bdd_ennval_of_bdd_Rval {α : Type*} {f : α → ℝ}
  (f_bdd : bdd_Rval f) : bdd_ennval (ennreal.of_real ∘ f) :=
begin
  cases f_bdd with c hc ,
  use (c.to_nnreal) ,
  intros x ,
  apply ennreal.coe_mono ,
  apply real.to_nnreal_mono (le_trans (le_abs_self (f(x))) (hc x)) ,
end


lemma lim_R_of_lim_enn (s : ℕ → ennreal) (l : ennreal) 
  (hlim : tendsto s at_top (𝓝 l)) (hfin : l ≠ ⊤) : 
    tendsto (ennreal.to_real ∘ s) at_top (𝓝 (ennreal.to_real l)) :=
begin
  have cont_at : continuous_at ennreal.to_real l
    := continuous_on.continuous_at ennreal_to_real_continuous_on_nnreal (nnreal_nbhd_finite_ennreal l hfin) , 
  exact tendsto.comp cont_at hlim ,
end


lemma cont_R_of_cont_bdd_enn {α : Type*} [topological_space α]
  (f : α → ennreal) (f_cont : continuous f) (f_bdd : bdd_ennval f) :
    continuous (ennreal.to_real ∘ f) :=
begin
  apply continuous_iff_continuous_at.mpr ,
  intros a ,
  set x := f(a) with hx ,
  have x_fin : x ≠ ⊤ := finval_of_bdd_ennval f_bdd a , 
  have cont_at₁ := continuous_iff_continuous_at.mp f_cont a ,
  have cont_at₂ : continuous_at ennreal.to_real x
    := continuous_on.continuous_at ennreal_to_real_continuous_on_nnreal (nnreal_nbhd_finite_ennreal x x_fin) , 
  exact @continuous_at.comp α ennreal ℝ _ _ _ ennreal.to_real f a cont_at₂ cont_at₁ ,
end


lemma cont_enn_of_cont_R {α : Type*} [topological_space α] (f : α → ℝ) (f_cont : continuous f) : 
  continuous (ennreal.of_real ∘ f) 
    := continuous.comp (ennreal.continuous_of_real) f_cont 


lemma le_of_forall_pos_le_add_nnreal (a b : nnreal) : 
  (∀ (ε : nnreal) , (ε > 0) → (a ≤ b + ε)) → a ≤ b :=
begin
  exact nnreal.le_of_forall_pos_le_add ,
end


lemma tendsto_of_ev_same {α β : Type*} {Fα : filter α} {Fβ : filter β}
  (f g : α → β) (h_ev_eq : ∃ (S : set α) , S ∈ Fα.sets ∧ 
    ∀ x , x ∈ S → f(x) = g(x) ) :
      tendsto f Fα Fβ → tendsto g Fα Fβ :=
begin
  intro tends_f ,
  cases h_ev_eq with S hS ,
  intros T hT ,
  have key := Fα.inter_sets hS.1 (tends_f hT),
  have eq_fg : S ∩ f⁻¹' T = S ∩ g⁻¹' T ,
  { ext x ,
    simp only [mem_inter_eq, mem_preimage, and.congr_right_iff] ,
    intro hxS ,
    rwa hS.2 x , } ,  
  rw eq_fg at key ,
  exact Fα.sets_of_superset key (set.inter_subset_right _ _ ) ,
end


lemma lim_R_of_ev_same (x y : ℕ → ℝ)
  (hevsame : ∃ (m : ℕ), ∀ (k : ℕ) , k ≥ m → x(k) = y(k))
  (hlim : tendsto x at_top (𝓝 0)) :
    tendsto y at_top (𝓝 0) :=
begin
  apply tendsto_of_ev_same x y ,
  { cases hevsame with m hm ,
    set S := { k : ℕ | k ≥ m } ,
    have mem : S ∈ at_top.sets := mem_at_top m ,
    use [ S , mem ] ,
    exact hm , } , 
  exact hlim ,
end


lemma lim_enn_of_ev_same (x y : ℕ → ennreal)
  (hevsame : ∃ (m : ℕ), ∀ (k : ℕ) , k ≥ m → x(k) = y(k))
  (hlim : tendsto x at_top (𝓝 0)) :
    tendsto y at_top (𝓝 0) :=
begin
  apply tendsto_of_ev_same x y ,
  { cases hevsame with m hm ,
    set S := { k : ℕ | k ≥ m } ,
    have mem : S ∈ at_top.sets := mem_at_top m ,
    use [ S , mem ] ,
    exact hm , } , 
  exact hlim ,
end


lemma of_real_lt_of_lt_to_real {x : ℝ} {z : ennreal} (x_lt_z : x < z.to_real) (x_nn : 0 ≤ x) : 
  ennreal.of_real(x) < z :=
begin
  by_cases z_top : z = ⊤ ,
  { rw z_top ,
    exact lt_top_iff_ne_top.mpr (@ennreal.of_real_ne_top x) , } ,
  { have le : ennreal.of_real x ≤ z := ennreal.of_real_le_of_le_to_real (le_of_lt x_lt_z) ,
    have neq : ennreal.of_real x ≠ z ,
    { by_contra con ,
      push_neg at con ,
      rw ←con at x_lt_z ,
      rw (ennreal.to_real_of_real x_nn) at x_lt_z ,
      linarith , } ,
    exact (ne.le_iff_lt neq).mp le , } ,
end


lemma of_real_mono : monotone ennreal.of_real :=
begin
  intros x y hxy ,
  exact ennreal.of_real_le_of_real hxy ,
end


lemma of_real_lt_of_lt {x y : ℝ} (x_nn : 0 ≤ x) (x_lt_y : x < y) : 
  ennreal.of_real x < ennreal.of_real y :=
begin
  have ne : ennreal.of_real x ≠ ennreal.of_real y ,
  { intros h ,
    have rw_x : (ennreal.of_real x).to_real = x := ennreal.to_real_of_real x_nn ,
    have rw_y : (ennreal.of_real y).to_real = y := ennreal.to_real_of_real (le_of_lt (lt_of_le_of_lt x_nn x_lt_y)) ,
    have eq : (ennreal.of_real x).to_real = (ennreal.of_real y).to_real := congr_arg ennreal.to_real h ,
    rw [rw_x , rw_y] at eq ,
    apply ne_of_lt x_lt_y ,
    rwa eq at x_lt_y , } ,
  have le : ennreal.of_real x ≤ ennreal.of_real y := of_real_mono (le_of_lt x_lt_y) ,
  exact (ne.le_iff_lt).mp le ,
end


lemma of_real_lt_of_real {x y : ℝ} (hxy : ennreal.of_real x < ennreal.of_real y) : x < y :=
begin
  have x_ne_top : ennreal.of_real x ≠ ⊤ := ennreal.of_real_ne_top ,
  have y_gt' : 0 < ennreal.of_real y := pos_of_gt hxy ,
  have y_gt : 0 < y := ennreal.of_real_pos.mp y_gt' ,
  by_contra x_too_large ,
  simp only [not_lt] at x_too_large , 
  have x_ge := ennreal.of_real_le_of_real x_too_large ,
  exact not_lt.mpr (le_refl (ennreal.of_real x)) (lt_of_lt_of_le hxy x_ge) ,
end



end portmanteau_comeonlean_lemmas

end portmanteau


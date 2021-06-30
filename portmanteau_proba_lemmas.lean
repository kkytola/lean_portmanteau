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
import order.liminf_limsup
import order.complete_lattice
import portmanteau_limsup_lemmas



noncomputable theory
open set 
open tactic
open classical
open measure_theory
open measurable_space
open metric_space
open borel_space
open filter
open order
open_locale topological_space ennreal big_operators


namespace portmanteau


section portmanteau_probability_lemmas


lemma proba_muniv {β : Type*} {mβ : measurable_space β}
  (Pr : measure β) [hPr : probability_measure Pr] :
    Pr univ = 1 := measure_univ


lemma proba_le_one {β : Type*} {mβ : measurable_space β}
  (Pr : measure β) [hPr : probability_measure Pr] (A : set β) :
    Pr A ≤ 1 :=
begin
  have le_univ : Pr A ≤ Pr univ := Pr.to_outer_measure.mono (subset_univ A) ,
  rwa (proba_muniv Pr) at le_univ ,
end


lemma proba_finite {β : Type*} {mβ : measurable_space β}
  (Pr : measure β) [hPr : probability_measure Pr] (A : set β) :
    Pr A < ⊤ :=
begin
  exact lt_of_le_of_lt (proba_le_one Pr A) ennreal.one_lt_top ,
end


lemma proba_compl {β : Type*} {mβ : measurable_space β}
  {A : set β} (Pr : measure β) [hPr : probability_measure Pr]
  (mble_A : measurable_set A) :
    Pr Aᶜ = 1 - Pr (A) :=
begin
  have key := measure_compl mble_A (proba_finite Pr A) ,
  rwa proba_muniv Pr at key ,
end


lemma finite_integral_of_bdd_ennrealval {β : Type*} {mβ : measurable_space β}
  (μ : measure β) [μ_fin : probability_measure μ]
  (f : β → ennreal) (f_bdd : bdd_ennval f) :
     lintegral μ f < ⊤ :=
begin
  cases f_bdd with c hc ,
  have bdd' : f ≤ (λ b , c) := hc ,
  have integr_bdd := @lintegral_mono _ _ μ _ _ bdd' ,
  have const_integr : lintegral μ (λ b , c) = c * (μ(univ)) ,
  { rw ← set_lintegral_const univ c ,
    simp only [measure.restrict_univ] , } ,
  have total : (c : ennreal) * (μ(univ)) < ⊤ ,
  { rw (proba_muniv μ) ,
    simp only [mul_one, ennreal.coe_lt_top] , } ,
  rw ← const_integr at total ,
  exact lt_of_le_of_lt integr_bdd total , 
end


abbreviation indic {β : Type*} (A : set β) : β → ennreal :=
  indicator A (λ (b : β) , (1 : ennreal))


def indic' {β : Type*} (A : set β) : β → ennreal :=
  indicator A (λ (b : β) , (1 : ennreal))


lemma indic_rw {β : Type*} (A : set β) :
  indic A = set.indicator A (λ b , (1 : ennreal))
    := by refl


lemma indic_val_zero_or_one {β : Type*} (A : set β) (x : β):
  indic A x = 0 ∨ indic A x = 1 :=
begin
  by_cases x ∈ A ; simp [h] ,
end


lemma indic_le_one {β : Type*} (A : set β) (x : β):
  indic A x ≤ 1 :=
begin
  cases (indic_val_zero_or_one A x) with hval hval ,
  { simp only [hval, zero_le] , } ,
  { rw hval , 
    tidy , } ,
end


lemma integral_indic {β : Type*}
  {mβ : measurable_space β} (ν : measure β)
  (E : set β) (mble_E : measurable_set E) :
    lintegral ν (indic E) = ν(E) :=
begin
  rw [indic_rw , ← @set_lintegral_one β mβ ν E , lintegral_indicator ] ,
  exact mble_E ,
end


lemma indic_val_one_iff {β : Type*} (A : set β) (x : β):
  indic A x = 1 ↔ x ∈ A :=
begin
  by_cases x ∈ A ; simp [h] ,
end


lemma indic_val_zero_iff {β : Type*} (A : set β) (x : β):
  indic A x = 0 ↔ x ∉ A :=
begin
  by_cases x ∈ A ; simp [h] ,
end


lemma indic_univ {β : Type*} :
  indic (univ : set β) = (λ b , 1) :=
begin
  funext x ,
  exact (indic_val_one_iff (univ : set β) x).mpr (mem_univ x) ,
end


lemma indic_preim_one_subset {β : Type*} [measurable_space β] (A : set β) :
  ∀ (S : set ennreal) , ((1:ennreal) ∈ S) → A ⊆ (indic A)⁻¹' S :=
begin
  intros S hSone a ha ,
  rw [mem_preimage , (indic_val_one_iff A a).mpr ha] ,
  exact hSone ,
end


lemma indic_preim_one_no_zero_subset {β : Type*} [measurable_space β] (A : set β) :
  ∀ (S : set ennreal) , ((1:ennreal) ∈ S) → ((0:ennreal) ∉ S) → A = (indic A)⁻¹' S :=
begin
  intros S hSone hSnozero ,
  have sub := indic_preim_one_subset A S hSone ,
  apply le_antisymm ,
  { exact sub , } ,
  intros a ha ,
  rw ← indic_val_one_iff ,
  rw mem_preimage at ha ,
  cases indic_val_zero_or_one A a with opt opt' ,
  { rw opt at ha ,
    contradiction , } , 
  { assumption , } , 
end


lemma indic_preim_one_and_zero_subset {β : Type*} [measurable_space β] (A : set β) :
  ∀ (S : set ennreal) , ((1:ennreal) ∈ S) → ((0:ennreal) ∈ S) → univ = (indic A)⁻¹' S :=
begin
  intros S hSone hSnozero ,
  apply le_antisymm ,
  swap ,
  { simp only [le_eq_subset, subset_univ], } , 
  intros x hx ,
  rw mem_preimage ,
  cases indic_val_zero_or_one A x with opt opt ;
  { rw opt at * ,
    assumption , } , 
end


lemma indic_mble_iff {β : Type*} [measurable_space β] (A : set β) :
  measurable (indic A) ↔ measurable_set A :=
begin
  split ,
  { have preim : (indic A)⁻¹' {1} = A ,
    { ext x ,
      exact indic_val_one_iff A x , } ,
    have sing_meas : measurable_set ({1} : set ennreal) := measurable_set_singleton 1 ,
    intro hmeas ,
    specialize hmeas sing_meas ,
    rwa preim at hmeas , } , 
  intros mble_A ,
  suffices : ∀ (B : set ennreal) , (1:ennreal) ∈ B → measurable_set B → measurable_set ((indic A)⁻¹' B) ,
  { intros B hB ,
    by_cases Hone : (1:ennreal) ∈ B ,
    { exact this B Hone hB , } ,
    have mblecompl := this Bᶜ (mem_compl Hone) (by simp [hB]) ,
    tidy , } ,
  intros B one_B mble_B ,
  by_cases hzero : (0:ennreal) ∈ B ,
  { rw ← indic_preim_one_and_zero_subset A B one_B hzero ,
    exact measurable_set.univ , } , 
  { rw ← indic_preim_one_no_zero_subset A B one_B hzero ,
    assumption , } , 
end


lemma indic_mono {β : Type*} (A B : set β) (hAB : A ⊆ B):
  indic A ≤ indic B :=
begin
  intro x ,
  by_cases x ∈ A ,
  { have indvalA := (indic_val_one_iff A x).mpr h ,
    have indvalB := (indic_val_one_iff B x).mpr (hAB h) ,
    rw [indvalA , indvalB] ,
    exact ennreal.coe_to_nnreal_le_self , } ,
  { have indval := (indic_val_zero_iff A x).mpr h ,
    rw indval ,
    have val_opt := indic_val_zero_or_one B x ,
    cases val_opt ; { rw val_opt , simp , } , } ,
end


abbreviation is_decreasing_seq {τ : Type*} [preorder τ] (s : ℕ → τ) :=
  @monotone ℕ (order_dual τ) _ _ s


abbreviation is_decreasing_seq' {τ : Type*} [has_le τ] (s : ℕ → τ) :=
  ∀ (n m : ℕ) , n ≤ m → s(m) ≤ s(n)


lemma is_decreasing_seq_iff {τ : Type*} [preorder τ] {s : ℕ → τ} :
  is_decreasing_seq s ↔ ∀ (n m : ℕ) , n ≤ m → s(m) ≤ s(n) := by refl


lemma lim_le_of_decr {τ : Type*} [ord : linear_order τ] [topo : topological_space τ]
  [ord_topo : order_topology τ] (s : ℕ → τ) (l : τ)
  (h_decr : @monotone ℕ (order_dual τ) _ _ s) (h_lim : tendsto s at_top (𝓝 l)) :
    ∀ n , l ≤ s(n) :=
begin
  intros m₀ ,
  by_contra under_lim ,
  simp at under_lim ,
  set U := Ioi (s(m₀)) with hU ,
  have hU_nbhd : U ∈ 𝓝 l := Ioi_mem_nhds under_lim ,
  have too_low : ∀ (n : ℕ) , n ≥ m₀ → s(n) ∉ U ,
  { intros n hn ,
    simp ,
    exact h_decr hn , } ,
  have key := filter.tendsto_at_top'.mp h_lim U hU_nbhd ,
  cases key with n₀ hn₀ ,
  set k := max n₀ m₀ with hk ,
  have k_ge_n₀ : n₀ ≤ k := le_max_left n₀ m₀ ,
  have k_ge_m₀ : m₀ ≤ k := le_max_right n₀ m₀ ,
  specialize hn₀ k k_ge_n₀ ,
  specialize too_low k k_ge_m₀ ,
  contradiction ,
end


structure ptwise_decr_lim_ennreal {β : Type*} (f : β → ennreal) :=
  (funseq : ℕ → (β → ennreal) )
  (decr : is_decreasing_seq funseq )
  (limit : ∀ (b : β) , lim_enn (λ n , (funseq n b)) (f(b)) )


lemma ptwise_decr_lim_ennreal_lim_le {β : Type*} {f : β → ennreal} (fseq : ptwise_decr_lim_ennreal f) :
  ∀ n , f ≤ fseq.funseq(n) :=
begin
  intros n x ,
  have decr_at_x : is_decreasing_seq (λ (n : ℕ) , ((fseq.funseq(n))(x)) ) ,
  { intros n m hnm ,
    dsimp ,
    exact fseq.decr hnm x , } , 
  exact lim_le_of_decr (λ (n : ℕ) , ((fseq.funseq(n))(x)) ) (f(x)) decr_at_x (fseq.limit x) n ,
end


structure ptwise_decr_mble_lim_ennreal {β : Type*}
  (msβ : measurable_space β) (f : β → ennreal) 
    extends (ptwise_decr_lim_ennreal f) :=
  (mble : ∀ (n : ℕ) , @measurable β ennreal msβ _ (funseq(n)) )


def ptwise_decr_lim_ennreal' {β : Type*}
  (fseq : ℕ → (β → ennreal)) (f : β → ennreal) :=
    is_decreasing_seq (λ n , (fseq n)) ∧
    ( ∀ (b : β) , lim_enn (λ n , (fseq n b)) (f(b)) )


lemma measure_of_mble_decr_approx_indicator {β : Type*}
  {msβ : measurable_space β} (ν : measure β)
  (E : set β) (mble_E : measurable_set E)
  (fseq : ptwise_decr_mble_lim_ennreal msβ (indic E) )
  (finite_integral : lintegral ν (fseq.funseq(0)) < ⊤) :
    lim_enn ( λ n , lintegral ν (fseq.funseq(n)) ) (ν(E)) :=
begin
  have indicator_inf : (λ (b : β), ⨅ (n : ℕ), fseq.funseq n b) = indic E ,
  { funext b ,
    have ptwise_decr : ∀ (n m : ℕ) , n ≤ m → fseq.funseq m b ≤ fseq.funseq n b  ,
    { intros n m hnm ,
      exact fseq.decr hnm b , } , 
    exact infi_eq_of_tendsto ptwise_decr (fseq.limit b) , } ,
  rw ← integral_indic ν E mble_E ,
  have integr_decr : ∀ (n m : ℕ) , n ≤ m →
      lintegral ν (fseq.funseq(m)) ≤ lintegral ν (fseq.funseq(n)) ,
  { intros n m hnm ,
    exact lintegral_mono (fseq.decr hnm) , } ,
  have key := lintegral_infi fseq.mble fseq.decr finite_integral ,
  dsimp at key ,
  rw indicator_inf at key ,
  rw key ,
  exact tendsto_at_top_infi integr_decr ,
end


lemma inv_nat_ennreal_antimono {n m : ℕ} :
  n ≤ m → (m : ennreal)⁻¹ ≤ (n : ennreal)⁻¹ :=
begin
  by_cases hn : (n = 0) ,
  { have infty : (n : ennreal)⁻¹ = ⊤ ,
    { rw hn ,
      simp only [ennreal.inv_zero, nat.cast_zero] , } ,
    rw infty ,
    simp only [implies_true_iff, le_top] , } ,
  { intros hnm ,
    have ineq : 1/m ≤ 1/n := nat.div_le_div_left hnm (zero_lt_iff.mpr hn) ,
    simp [ineq , hnm] , } ,
end


lemma exists_nat_one_div_lt_ennreal {z : ennreal} (zpos : 0 < z) :
  ∃ (n : ℕ) , (1/(n+1) : ennreal) < z :=
begin
  have key := ennreal.exists_inv_nat_lt (ne_of_gt zpos),
  cases key with n hn ,
  use n ,
  have le := inv_nat_ennreal_antimono (nat.le_succ n) ,
  have key := lt_of_le_of_lt le hn,
  have eq : (1/(n+1) : ennreal) = (n+1 : ennreal)⁻¹ := by simp only [one_div] ,
  rwa eq ,
end


lemma positive_levels_countable_union {γ : Type*} (g : γ → ennreal) :
  { y : γ | g y > 0} = (⋃ n , (λ (n : ℕ), { y : γ | g y > 1/(n+1)}) n) :=
begin
  suffices : { y : γ | g y > 0} ⊆ (⋃ n , (λ (n : ℕ), { y : γ | g y > 1/(n+1)}) n) ,
  { apply le_antisymm ,
    { exact this , } ,
    { intros x hx ,
      simp at * ,
      cases hx with n hn ,
      exact lt_of_le_of_lt (by simp) hn , } ,
    } ,
  intros x hx , 
  simp at * ,
  cases (exists_nat_one_div_lt_ennreal hx) with n hn ,
  use n ,
  have eq : (1/(n+1) : ennreal) = (n+1 : ennreal)⁻¹ := by simp only [one_div] ,
  rwa ← eq ,
end


lemma finitely_many_substantial_members_disjoint_union_finmeas {β ι : Type*}
  [mβ : measurable_space β] {ν : measure β}
  (B : set β) (B_mble : measurable_set B) (B_fin : ν(B) < ⊤) 
  (ε : ennreal) (ε_pos : 0 < ε)
  (A : ι → set β) (hAB : ∀ i , A(i) ⊆ B) 
  (A_mble : ∀ (i : ι), measurable_set (A i)) (h_disj : pairwise (disjoint on A))
  : set.finite {i : ι | ε ≤ ν(A(i))} :=
begin
  set substantial := {i : ι | ε ≤ ν(A(i))} with h_substantial ,
  by_contradiction hcontra ,
  have pickseq := set.infinite.nat_embedding _ hcontra ,
  set seq := (λ i, (pickseq.to_fun (i)).val ) with hseq ,
  have seq_inj : function.injective seq , 
  { intros i j hij ,
    simp only [hseq, function.embedding.to_fun_eq_coe, subtype.val_eq_coe] at hij,
    have eq : pickseq.to_fun(i) = pickseq.to_fun(j) ,
    { ext , exact hij , } ,
    exact pickseq.injective eq , } , 
  have seq_ran : ∀ i , seq(i) ∈ substantial ,
  { intros i ,
    have itoldyaso : (pickseq.to_fun(i)).val = seq(i) := by simp only [hseq] ,
    rw ← itoldyaso ,
    exact (pickseq.to_fun(i)).property , } , 
  have mbles : ∀ (i : ℕ) , measurable_set ( A (seq(i)) ) ,
  { intros i ,
    apply A_mble , } ,
  have disj : pairwise ( disjoint on (λ (i : ℕ) , A(seq(i)))) ,
  { intros i j hij b hb ,
    have hij' : (seq(i)) ≠ (seq(j)) := function.injective.ne seq_inj hij ,
    exact h_disj (seq i) (seq j) hij' hb , } ,
  have massive := @measure_Union β ℕ mβ ν _ _ disj mbles ,
  clear disj mbles ,
  dsimp at massive ,
  have large_terms : ∀ i , ε ≤ ν (A (seq(i))) := seq_ran ,
  have diverges : ∑' (i : ℕ), ν (A(seq(i))) = ⊤ ,
  { have le : ∑' (i : ℕ), ε ≤ ∑' (i : ℕ), ν (A(seq(i))) ,
    { exact ennreal.tsum_le_tsum large_terms , } ,
    have cst_sum := sum_infinitely_many_pos_const_ennreal ε ε_pos ,
    rw cst_sum at le ,
    exact eq_top_iff.mpr le , } , 
  rw diverges at massive ,
  have sub_mem : ∀ (i : ℕ) , A (seq(i)) ⊆ B := by simp only [hAB, forall_const] ,
  have sub : (⋃ (i : ℕ) , A (seq(i))) ⊆ B := Union_subset sub_mem ,
  have shouldnot' : ν (⋃ (i : ℕ) , A (seq(i))) ≤ ν (B) := measure_mono sub ,
  have shouldnot := lt_of_le_of_lt shouldnot' B_fin ,
  rw massive at shouldnot ,
  exact ennreal.not_lt_top.mpr rfl shouldnot ,
end


lemma pos_ennreal_union_ge_inv_nat_succ :
  {z : ennreal | 0 < z} = ⋃ (n : ℕ) , {z : ennreal | z ≥ 1/(n+1)} :=
begin
  apply le_antisymm ,
  { intros z hz ,
    rw mem_set_of_eq at hz ,
    simp_rw [mem_Union , mem_set_of_eq] ,
    cases (exists_nat_one_div_lt_ennreal hz) with n hn ,
    use n ,
    exact le_of_lt hn , } ,
  { intros z hz ,
    rw mem_Union at hz ,
    cases hz with n hn ,
    rw mem_set_of_eq at hn ,
    have lt : (0 : ennreal) < (1/(n+1) :ennreal) 
      := by simp only [one_div, ennreal.add_eq_top, ennreal.nat_ne_top, ne.def, ennreal.one_ne_top, not_false_iff, ennreal.inv_pos, or_self],
    exact lt_of_lt_of_le lt hn , } ,
end


lemma pos_ennreal_union_ge_inv_nat :
  {z : ennreal | 0 < z} = ⋃ (n : ℕ) , {z : ennreal | z ≥ 1/n} :=
begin
  apply le_antisymm ,
  { intros z hz ,
    rw mem_set_of_eq at hz ,
    simp_rw [mem_Union , mem_set_of_eq] ,
    cases (exists_nat_one_div_lt_ennreal hz) with n hn ,
    use n+1 ,
    exact le_of_lt hn , } ,
  { intros z hz ,
    rw mem_Union at hz ,
    cases hz with n hn ,
    rw mem_set_of_eq at hn ,
    have lt : (0 : ennreal) < (1/n :ennreal) 
      := by simp only [one_div, ennreal.add_eq_top, ennreal.nat_ne_top, ne.def, ennreal.one_ne_top, not_false_iff, ennreal.inv_pos, or_self],
    exact lt_of_lt_of_le lt hn , } ,
end


lemma ennval_pos_union_ge_inv_nat_succ {γ : Type*} (f : γ → ennreal) :
  {x : γ | 0 < f x} = ⋃ (n : ℕ) , {x : γ | f x ≥ 1/(n+1)} :=
begin
  have lhs_preim : {x : γ | 0 < f x} = f⁻¹' {z : ennreal | 0 < z} := by refl ,
  rw [ lhs_preim , pos_ennreal_union_ge_inv_nat_succ , preimage_Union ] ,
  simp only [preimage_set_of_eq] ,
end


lemma ennval_pos_union_ge_inv_nat {γ : Type*} (f : γ → ennreal) :
  {x : γ | 0 < f x} = ⋃ (n : ℕ) , {x : γ | f x ≥ 1/n} :=
begin
  have lhs_preim : {x : γ | 0 < f x} = f⁻¹' {z : ennreal | 0 < z} := by refl ,
  rw [ lhs_preim , pos_ennreal_union_ge_inv_nat , preimage_Union ] ,
  simp only [preimage_set_of_eq] ,
end


lemma countably_many_positive_measure_members_disjoint_union {β ι : Type*}
  [mβ : measurable_space β] (ν : measure β) 
  (B : set β) (B_mble : measurable_set B) (B_fin : ν(B) < ⊤) 
  (A : ι → set β) (hAB : ∀ i , A(i) ⊆ B) 
  (A_mble : ∀ (i : ι), measurable_set (A i)) (h_disj : pairwise (disjoint on A)) :
    set.countable { i : ι | ν (A i) > 0} :=
begin
  set posmeas := { i : ι | ν (A i) > 0} with h_posmeas ,
  set fairmeas := λ (n : ℕ) , { i : ι | ν (A i) ≥ 1/n} with h_fairmeas ,
  have countable_union : posmeas = (⋃ n , fairmeas(n)) ,
  { exact ennval_pos_union_ge_inv_nat (λ (i : ι) , ν (A(i))) , } ,
  have countable_pieces : ∀ (n : ℕ) , set.countable (fairmeas(n)) ,
  { intros n ,
    suffices : set.finite (fairmeas(n)) ,
    { exact finite.countable this , } , 
    have pos : (0 : ennreal) < (1/n : ennreal) 
      := by simp only [one_div, ennreal.add_eq_top, ennreal.nat_ne_top, ne.def, ennreal.one_ne_top, not_false_iff, ennreal.inv_pos, or_self] ,
    apply finitely_many_substantial_members_disjoint_union_finmeas
      B B_mble B_fin (1/n : ennreal) pos A hAB A_mble h_disj , } ,
  rw countable_union ,
  exact countable_Union countable_pieces ,
end


lemma countably_many_positive_measure_members_disjoint_union' {β ι : Type*}
  [mβ : measurable_space β] (ν : measure β) [hfin : probability_measure ν]
  (A : ι → set β) (h_mble : ∀ i , measurable_set (A i)) (h_disj : pairwise (disjoint on A)) :
  set.countable { i : ι | ν (A i) > 0} :=
begin
  set posmeas := { i : ι | ν (A i) > 0} with h_posmeas ,
  set fairmeas := λ (n : ℕ) , { i : ι | ν (A i) ≥ 1/n} with h_fairmeas ,
  have countable_union : posmeas = (⋃ n , fairmeas(n)) ,
  { exact ennval_pos_union_ge_inv_nat (λ (i : ι) , ν (A(i))) , } ,
  have countable_pieces : ∀ (n : ℕ) , set.countable (fairmeas(n)) ,
  { intros n ,
    suffices : set.finite (fairmeas(n)) ,
    { exact finite.countable this , } , 
    have pos : (0 : ennreal) < (1/n : ennreal) 
      := by simp only [one_div, ennreal.add_eq_top, ennreal.nat_ne_top, ne.def, ennreal.one_ne_top, not_false_iff, ennreal.inv_pos, or_self] ,
    exact finitely_many_substantial_members_disjoint_union_finmeas
      (univ : set β) (measurable_set.univ) (proba_finite ν _) 
      (1/n : ennreal) pos A (by simp only [subset_univ, implies_true_iff]) 
      h_mble h_disj , } ,
  rw countable_union ,
  exact countable_Union countable_pieces ,
end


lemma countably_many_level_sets_of_positive_measure {β γ : Type*}
  {mβ : measurable_space β} {mγ : measurable_space γ} (f : β → γ)
  [measurable_singleton_class γ]
  (mble_f : measurable f) (ν : measure β) (hfin : probability_measure ν) :
  set.countable { y : γ | ν (f⁻¹' {y}) > 0} :=
begin
  set posmeas := { y : γ | ν (f⁻¹' {y}) > 0} with hposmeas ,
  set fairmeas := λ (n : ℕ) , { y : γ | ν (f⁻¹' {y}) ≥ 1/n} with hfairmeas ,
  have countable_union' := ennval_pos_union_ge_inv_nat (λ y , ν (f⁻¹' {y})) ,
  have mbles : ∀ y , measurable_set (f⁻¹'{y}) ,
  { intros y ,
    apply mble_f ,
    exact measurable_set_eq , } ,
  have disjoints : pairwise (disjoint on (λ (y : γ) , (f⁻¹'{y}))) ,
  { intros y₁ y₂ hy x hx ,
    have fx_eq₁ : f x = y₁ := hx.1 ,
    have fx_eq₂ : f x = y₂ := hx.2 ,
    rw [←fx_eq₁ , ←fx_eq₂] at hy ,
    contradiction , } ,
  exact countably_many_positive_measure_members_disjoint_union 
        ν (univ : set β) (measurable_set.univ) (proba_finite ν _) 
        (λ (y : γ) , f⁻¹' {y}) (by simp only [subset_univ, implies_true_iff]) 
        mbles disjoints ,  
end



end portmanteau_probability_lemmas

end portmanteau

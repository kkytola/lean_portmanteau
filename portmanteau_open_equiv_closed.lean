/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import portmanteau_definitions
import portmanteau_topological_lemmas
import portmanteau_proba_lemmas



noncomputable theory
open measure_theory
open filter



namespace portmanteau

section portmanteau_open_equiv_closed



variables {α : Type} [topological_space α]


notation `borel_measure`(α) := @measure_theory.measure α (borel α)
notation `borel_set`(α) E := (borel α).measurable_set' E


lemma portmanteau_open_imp_closed_cond
  (μseq : ℕ → (borel_measure(α))) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : borel_measure(α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
  portmanteau_open μseq μ → portmanteau_closed μseq μ :=
begin
  intros hopcond F F_clos ,
  set G := Fᶜ with hG ,
  have G_open : is_open G := is_open_compl_iff.mpr F_clos ,
  specialize hopcond G G_open ,
  rw hG at hopcond ,
  have eq : μ Fᶜ = 1 - μ F := @proba_compl α (borel(α)) F μ μ_fin (closed_imp_borel F_clos) ,
  have eq_seq : (λ n , (μseq(n)) Fᶜ) = (λ n , 1 - (μseq(n)) F) ,
  { funext n ,
    exact @proba_compl α (borel(α)) F (μseq(n)) (μseq_fin(n)) (closed_imp_borel F_clos) , } ,
  rw [eq , eq_seq] at hopcond ,
  rw liminf_const_sub 1 (ennreal.one_ne_top) at hopcond ,
  have le₁ : μ(F) ≤ 1 := proba_le_one μ F ,
  have le₂ : limsup_enn (λ n , (μseq(n))(F)) ≤ 1 := limsup_le_of_le_ennreal (λ n , proba_le_one (μseq(n)) F) ,
  exact le_of_self_sub_le_self_sub_ennreal 1 _ _ ennreal.one_ne_top le₁ le₂ hopcond ,
end


lemma portmanteau_closed_imp_open_cond
  (μseq : ℕ → (borel_measure(α))) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : borel_measure(α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
  portmanteau_closed μseq μ → portmanteau_open μseq μ :=
begin
  intros hclcond G G_open ,
  set F := Gᶜ with hF ,
  have F_closed : is_closed F := is_closed_compl_iff.mpr G_open ,
  specialize hclcond F F_closed ,
  rw hF at hclcond ,
  have eq : μ Gᶜ = 1 - μ G := @proba_compl α (borel(α)) G μ μ_fin (open_imp_borel G_open) ,
  have eq_seq : (λ n , (μseq(n)) Gᶜ) = (λ n , 1 - (μseq(n)) G) ,
  { funext n ,
    exact @proba_compl α (borel(α)) G (μseq(n)) (μseq_fin(n)) (open_imp_borel G_open) , } ,
  rw [eq , eq_seq] at hclcond ,
  rw limsup_const_sub 1 (ennreal.one_ne_top) at hclcond ,
  have le₁ : μ(G) ≤ 1 := proba_le_one μ G ,
  have le₂ : liminf_enn (λ n , (μseq(n))(G)) ≤ 1 := liminf_le_of_le_ennreal (λ n , proba_le_one (μseq(n)) G) ,
  exact le_of_self_sub_le_self_sub_ennreal 1 _ _ ennreal.one_ne_top le₂ le₁ hclcond ,
end



lemma portmanteau_closed_and_open_cond_equivalent
  (μseq : ℕ → (borel_measure(α))) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : borel_measure(α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
  portmanteau_closed μseq μ ↔ portmanteau_open μseq μ :=
begin
  split ,
  { exact portmanteau_closed_imp_open_cond μseq μseq_fin μ μ_fin , } ,
  { exact portmanteau_open_imp_closed_cond μseq μseq_fin μ μ_fin , } ,
end



end portmanteau_open_equiv_closed

end portmanteau

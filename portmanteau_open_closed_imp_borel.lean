/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import portmanteau_definitions
import portmanteau_topological_lemmas
import portmanteau_open_equiv_closed



noncomputable theory
open measure_theory



namespace portmanteau

section portmanteau_open_closed_implies_borel



variables {α : Type} [topological_space α]


lemma portmanteau_open_closed_imp_borel_cond
  (μseq : ℕ → @measure_theory.measure α (borel α)) (μ : @measure_theory.measure α (borel α)) : 
    portmanteau_open μseq μ ∧ portmanteau_closed μseq μ
    → portmanteau_borel μseq μ :=
begin
  rintros ⟨ hopcond , hclcond ⟩ ,
  intros E hEborel hEnullbdry ,
  set Ecl := closure E with hEcl ,
  set Eint := interior E with hEint ,
  have h_E_subset_Ecl : E ⊆ Ecl := subset_closure ,
  have h_Eint_subset_E : Eint ⊆ E := interior_subset ,
  have ineq_E_le_Ecl := @measure_mono α (borel(α)) μ E Ecl subset_closure ,
  have ineq_E_le_Ecl_seq := (λ (n : ℕ) , @measure_mono α (borel(α)) (μseq(n)) E Ecl subset_closure ) ,
  have ineq_Eint_le_E := @measure_mono α (borel(α)) μ Eint E interior_subset ,
  have ineq_Eint_le_E_seq := (λ (n : ℕ) , @measure_mono α (borel(α)) (μseq(n)) Eint E interior_subset) ,
  have equalities := meas_eq_various_of_null_bdry μ E hEnullbdry ,
  have pt_limsup : limsup_enn (λ n , (μseq(n))(E)) ≤ μ(E) ,
  { calc limsup_enn (λ n , (μseq(n))(E))
        ≤ limsup_enn (λ n , (μseq(n))(Ecl))  : limsup_enn_mono ineq_E_le_Ecl_seq
    ... ≤ μ(Ecl)                             : hclcond Ecl is_closed_closure
    ... = μ(E)                               : by rw equalities.2 ,
    } ,
  have pt_liminf : μ(E) ≤ liminf_enn (λ n , (μseq(n))(E)) ,
  { calc μ(E) = μ(Eint)                      : by rw equalities.1
    ... ≤ liminf_enn (λ n , (μseq(n))(Eint)) : hopcond Eint is_open_interior
    ... ≤ liminf_enn (λ n , (μseq(n))(E))    : liminf_enn_mono ineq_Eint_le_E_seq ,
    } ,
  have key := lim_eq_liminf_of_limsup_le_liminf_ennreal (le_trans pt_limsup pt_liminf) ,
  suffices : liminf_enn (λ n , (μseq(n))(E)) = μ(E) ,
  { rw ← this ,
    exact key , } , 
  apply le_antisymm ,
  { exact le_trans (liminf_le_limsup_enn (λ n , (μseq(n))(E))) pt_limsup , } ,
  { exact pt_liminf , } ,
end


lemma portmanteau_open_imp_borel
  (μseq : ℕ → @measure_theory.measure α (borel α)) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : @measure_theory.measure α (borel α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
    portmanteau_open μseq μ → portmanteau_borel μseq μ :=
begin
  intros hopcond ,
  have hclcond := portmanteau_open_imp_closed_cond μseq μseq_fin μ μ_fin hopcond ,
  exact portmanteau_open_closed_imp_borel_cond μseq μ ⟨ hopcond , hclcond ⟩ ,
end


lemma portmanteau_closed_imp_borel
  (μseq : ℕ → @measure_theory.measure α (borel α)) 
  (μseq_fin : ∀ (n : ℕ) , @probability_measure α (borel(α)) (μseq(n)))
  (μ : @measure_theory.measure α (borel α)) (μ_fin : @probability_measure α (borel(α)) μ) : 
    portmanteau_closed μseq μ → portmanteau_borel μseq μ :=
begin
  intros hclcond ,
  have hopcond := portmanteau_closed_imp_open_cond μseq μseq_fin μ μ_fin hclcond ,
  exact portmanteau_open_closed_imp_borel_cond μseq μ ⟨ hopcond , hclcond ⟩ ,
end


end portmanteau_open_closed_implies_borel

end portmanteau

/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import tactic 
import measure_theory.measurable_space
import measure_theory.borel_space


noncomputable theory
open set 
open measure_theory
open measurable_space
open borel_space


namespace portmanteau

section portmanteau_topological_lemmas


variables {α : Type*} [topological_space α]


lemma meas_eq_various_of_null_bdry (μ : @measure_theory.measure α (borel α)) (E : set α) :
  (μ(frontier E) = 0) → (μ(interior E) = μ(E)) ∧ (μ(closure E) = μ(E)) :=
begin
  intro hEnullbdry ,
  have ineq_E_le_Ecl := @measure_mono α (borel(α)) μ E (closure E) subset_closure ,
  have ineq_Eint_le_E := @measure_mono α (borel(α)) μ (interior E) E interior_subset ,
  have surpr := @measure_union_le α (borel(α)) μ (interior E) (frontier E) ,
  rw ← closure_eq_interior_union_frontier at surpr ,
  simp [hEnullbdry] at surpr ,
  have mono := @measure_mono α (borel(α)) μ (interior E) (closure E) interior_subset_closure ,
  have key := le_antisymm mono surpr ,
  split ,
  { apply le_antisymm ,
    { assumption , } ,
    rw key ,
    assumption , } , 
  { apply le_antisymm ,
    { rw ← key ,
      assumption , } , 
    assumption , } ,
end


lemma open_imp_borel {γ : Type*} [top_γ : topological_space γ]
  {G : set γ} : is_open G → (borel γ).measurable_set' G 
    := measurable_set_generate_from 


lemma closed_imp_borel {γ : Type*} [top_γ : topological_space γ]
  {F : set γ} : is_closed F → (borel γ).measurable_set' F :=
begin
  set G := Fᶜ with hG ,
  have FeqGc := compl_compl F ,
  rw ← hG at FeqGc , 
  intro hFclosed ,
  have Gmble := open_imp_borel (is_open_compl_iff.mpr hFclosed) ,
  rw ← FeqGc ,
  exact (borel γ).measurable_set_compl G Gmble ,
end


lemma compl_frontier {γ : Type*} [topological_space γ] (A : set γ) :
  (frontier A)ᶜ = (interior A) ∪ (interior (Aᶜ)) :=
begin
  have fact := @closure_eq_compl_interior_compl γ _ Aᶜ , 
  rw compl_compl at fact ,
  suffices : frontier A = (interior A)ᶜ ∩ (interior (Aᶜ))ᶜ ,
  { rw this ,
    rw compl_inter (interior A)ᶜ (interior (Aᶜ))ᶜ ,
    repeat {rw compl_compl ,} , } , 
  rw [←frontier_compl A , ←fact] ,
  exact diff_eq (closure (Aᶜ)) (interior (Aᶜ)) ,
end


lemma interior_preimage {β γ : Type*}
  [topological_space β] [topological_space γ]
  (G : set γ) (f : β → γ) (hf : continuous f) :
    f⁻¹' (interior G) ⊆ interior (f⁻¹'(G)) :=
begin
  apply interior_maximal ,
  { have Gint_ss_G : (interior G) ⊆ G := interior_subset ,
    exact preimage_mono Gint_ss_G , } ,
  { have interior_open : is_open (interior G) := is_open_interior ,
    exact continuous_def.mp hf (interior G) interior_open , } ,
end


lemma frontier_preimage {β γ : Type*}
  [topological_space β] [topological_space γ]
  (A : set γ) (f : β → γ) (hf : continuous f) :
    frontier (f⁻¹'(A)) ⊆ f⁻¹'(frontier A) :=
begin
  apply (@compl_subset_compl β (f⁻¹'(frontier A)) (frontier (f⁻¹'(A)))).mp,
  rw [compl_frontier _ , ←preimage_compl , compl_frontier _ , preimage_union ] ,
  have one := @interior_preimage β γ _ _ A f hf ,
  have two := @interior_preimage β γ _ _ (Aᶜ) f hf ,
  exact union_subset_union one two ,
end



end portmanteau_topological_lemmas

end portmanteau


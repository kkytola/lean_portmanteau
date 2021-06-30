/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import topology.instances.real
import topology.instances.ennreal
import portmanteau_comeonlean_lemmas



noncomputable theory
open set 
open filter
open_locale topological_space


namespace portmanteau


abbreviation liminf_R (s : ℕ → ℝ) : ℝ := liminf at_top s

abbreviation limsup_R (s : ℕ → ℝ) : ℝ := limsup at_top s

abbreviation liminf_enn (s : ℕ → ennreal) : ennreal := liminf at_top s

abbreviation limsup_enn (s : ℕ → ennreal) : ennreal := limsup at_top s

abbreviation lim_R (s : ℕ → ℝ) (l : ℝ) : Prop := tendsto s at_top (𝓝 l)

abbreviation lim_enn (s : ℕ → ennreal) (l : ennreal) : Prop := tendsto s at_top (𝓝 l)

lemma lim_R_rw (s : ℕ → ℝ) (l : ℝ) : lim_R s l = tendsto s at_top (𝓝 l) := by refl

lemma liminf_enn_rw {s : ℕ → ennreal} : liminf_enn s = liminf at_top s := by refl

lemma limsup_enn_rw {s : ℕ → ennreal} : limsup_enn s = limsup at_top s := by refl


section portmanteau_limsup_liminf_lemmas


lemma liminf_le_limsup_enn (s : ℕ → ennreal) :
  (liminf_enn s) ≤ (limsup_enn s) :=
begin
  apply @liminf_le_limsup ennreal _ _ _ _ s ,
  exact at_top_ne_bot ,
end


lemma lim_eq_liminf_of_limsup_le_liminf_ennreal {s : ℕ → ennreal}
  (hle : limsup_enn s ≤ liminf_enn s ) : 
    lim_enn (s) (liminf_enn s)  :=
begin
  have heq : limsup_enn s = liminf_enn s := le_antisymm hle (liminf_le_limsup_enn s) ,
  set l := liminf_enn s with hl,
  exact tendsto_of_liminf_eq_limsup hl heq ,
end


lemma lim_eq_limsup_of_limsup_le_liminf_ennreal {s : ℕ → ennreal}
  (hle : limsup_enn s ≤ liminf_enn s ) : 
    lim_enn s (limsup_enn s) :=
begin
  rw le_antisymm hle (liminf_le_limsup_enn s) ,
  exact lim_eq_liminf_of_limsup_le_liminf_ennreal hle ,
end


lemma lim_eq_limsup_ennreal {s : ℕ → ennreal} {l : ennreal} (hlim : lim_enn s l ) :
  limsup_enn s = l := tendsto.limsup_eq hlim 


lemma lim_eq_liminf_ennreal {s : ℕ → ennreal} {l : ennreal} (hlim : lim_enn s l ) :
  liminf_enn s = l := tendsto.liminf_eq hlim 


lemma limsup_le_of_le_ennreal {s : ℕ → ennreal} {b : ennreal} (hb : ∀ n , s(n) ≤ b ) :
  limsup_enn s ≤ b :=
begin
  have key : s ≤ᶠ[at_top] (λ n , b) := eventually_of_forall hb ,
  have le := limsup_le_limsup key ,
  have lim : tendsto (λ (n:ℕ) , b) at_top (𝓝 b) := tendsto_const_nhds ,
  have eq : at_top.limsup (λ n , b) = b := lim_eq_limsup_ennreal lim ,
  rwa eq at le ,
end


lemma liminf_le_of_le_ennreal {s : ℕ → ennreal} {b : ennreal} (hb : ∀ n , s(n) ≤ b ) :
  liminf_enn s ≤ b :=
begin
  have key : s ≤ᶠ[at_top] (λ n , b) := eventually_of_forall hb ,
  have le := liminf_le_liminf key ,
  have lim : tendsto (λ (n:ℕ) , b) at_top (𝓝 b) := tendsto_const_nhds ,
  have eq : at_top.liminf (λ n , b) = b := lim_eq_liminf_ennreal lim ,
  rwa eq at le ,
end


-- TODO: Why does Limsup_le_Limsup_of_le not work?
lemma limsup_enn_mono {s t : ℕ → ennreal} (hst : ∀ (n : ℕ) , s(n) ≤ t(n)) :
    limsup_enn s ≤ limsup_enn t :=
begin
  have relax : s ≤ᶠ[at_top] t ,
  { apply eventually_of_mem (@univ_mem_sets ℕ at_top) ,
    intros n hn ,
    exact hst n , } ,
  exact limsup_le_limsup relax ,
end


-- TODO: Why does Liminf_le_Liminf_of_le not work?
lemma liminf_enn_mono {s t : ℕ → ennreal} (hst : ∀ (n : ℕ) , s(n) ≤ t(n)) :
    liminf_enn s ≤ liminf_enn t :=
begin
  have relax : s ≤ᶠ[at_top] t ,
  { apply eventually_of_mem (@univ_mem_sets ℕ at_top) ,
    intros n hn ,
    exact hst n , } ,
  exact liminf_le_liminf relax ,
end


lemma Sup_neg (A : set ℝ) : Sup {x : ℝ | -x ∈ A} = - Inf A :=
begin
  set mA := {x : ℝ | -x ∈ A} with hmA ,
  set z := Sup mA with hz ,
  have key := real.Inf_def A ,
  rw key ,
  simp ,
end


lemma Inf_neg (A : set ℝ) : Inf {x : ℝ | -x ∈ A} = - Sup A :=
begin
  set mA := {x : ℝ | -x ∈ A} with hmA ,
  have key := Sup_neg mA ,
  set mmA := {x : ℝ | -x ∈ mA} with hmmA ,
  have AmmA : A = mmA := by simp [hmA , hmmA],
  rw [AmmA, key] ,
  simp ,
end


lemma liminf_neg {s : ℕ → ℝ} :
    liminf_R (-s) = - limsup_R s :=
begin
  set A := { a : ℝ | ∃ (a_1 : ℕ) , ∀ (b : ℕ) , a_1 ≤ b → s b ≤ a } with hA ,
  set mA := { a : ℝ | -a ∈ A } with hmA ,
  have mA_rw : mA = { a : ℝ | ∃ (a_1 : ℕ) , ∀ (b : ℕ) , a_1 ≤ b → a ≤ - s b } ,
  { ext a ,
    rw mem_set_of_eq ,
    split ; -- hide in corners
    { intro h ,
      cases h with k hk ,
      use k ,
      intros l hl ,
      specialize hk l hl ,
      linarith , } ,
    } ,
  have ls_eq : limsup_R s = Inf A ,
  { change limsup at_top s = Inf A ,
    rw limsup_eq , 
    simp only [eventually_at_top] , } , 
  have li_eq : liminf_R (-s) = Sup mA ,
  { change liminf at_top (-s) = Sup mA ,
    rw liminf_eq , 
    simp only [mA_rw, pi.neg_apply, eventually_at_top] , } , 
  rw [li_eq, ls_eq] ,
  exact Sup_neg A ,
end


lemma limsup_neg {s : ℕ → ℝ} :
    limsup_R (-s) = - liminf_R s :=
begin
  set t := -s with ht ,
  have nt_rw : s = -t := by tidy ,
  have key := @liminf_neg t ,
  rw nt_rw ,
  linarith ,
end


-- TODO: should the following couple of lemmas be done in more generality?
-- Probably `complete_semilattice_Sup` and `order_topology` etc.
-- would be good general assumptions.
lemma f_Sup_eq_Sup_f_ennreal (f : ennreal → ennreal) (f_mono : monotone f) (f_cont : continuous f)
  (T : set ennreal) (nonemp_T : T.nonempty) : 
    Sup (f '' T) = f(Sup T) :=
begin
  have ub : ∀ y ∈ f '' T , y ≤ f (Sup T) ,
  { intros y hy ,
    rcases hy with ⟨ x , hxT , fx_eq_y ⟩ ,
    rw ← fx_eq_y ,
    exact f_mono (le_Sup hxT) , } ,
  have lub : ∀ (b : ennreal) , (∀ y ∈ f '' T , y ≤ b) → f (Sup T) ≤ b ,
  { have tends : tendsto f (𝓝 (Sup T)) (𝓝 (f (Sup T))) := continuous.tendsto f_cont (Sup T) ,
    have tends' : tendsto f (𝓝[T] (Sup T)) (𝓝 (f (Sup T))) := tendsto_nhds_within_of_tendsto_nhds tends ,
    have tada : is_lub T (Sup T) := is_lub_Sup T ,
    have key := is_lub.is_lub_of_tendsto _ tada nonemp_T tends' ,
    { intros b hb ,
      exact key.2 hb , } ,
    { intros a haT b hbT hab ,
      exact f_mono hab , } ,
    } ,
  apply le_antisymm ,
  { apply Sup_le ub , } ,
  { apply le_Sup_iff.mpr lub , } ,
end


lemma f_Inf_eq_Inf_f_ennreal (f : ennreal → ennreal) (f_mono : monotone f) (f_cont : continuous f)
  (T : set ennreal) (nonemp_T : T.nonempty) : 
    Inf (f '' T) = f(Inf T) :=
begin
  have lb : ∀ y ∈ f '' T , f (Inf T) ≤ y ,
  { intros y hy ,
    rcases hy with ⟨ x , hxT , fx_eq_y ⟩ ,
    rw ← fx_eq_y ,
    exact f_mono (Inf_le hxT) , } ,
  have glb : ∀ (b : ennreal) , (∀ y ∈ f '' T , b ≤ y) → b ≤ f (Inf T) ,
  { have tends : tendsto f (𝓝 (Inf T)) (𝓝 (f (Inf T))) := continuous.tendsto f_cont (Inf T) ,
    have tends' : tendsto f (𝓝[T] (Inf T)) (𝓝 (f (Inf T))) := tendsto_nhds_within_of_tendsto_nhds tends ,
    have inf_is_glb : is_glb T (Inf T) := is_glb_Inf T ,
    have key := is_glb.is_glb_of_tendsto _ inf_is_glb nonemp_T tends' ,
    { intros b hb ,
      exact key.2 hb , } ,
    { intros a haT b hbT hab ,
      exact f_mono hab , } ,
    } ,
  apply le_antisymm ,
  { apply Inf_le_iff.mpr glb , } ,
  { apply le_Inf lb , } ,
end


lemma f_Sup_eq_Inf_f_ennreal (f : ennreal → ennreal) (f_antimono : @monotone ennreal (order_dual(ennreal)) _ _ f) (f_cont : continuous f)
  (T : set ennreal) (nonemp_T : T.nonempty) : Inf (f '' T) = f(Sup T) :=
begin
  have lb : ∀ y ∈ f '' T , f (Sup T) ≤ y,
  { intros y hy ,
    rcases hy with ⟨ x , hxT , fx_eq_y ⟩ ,
    rw ← fx_eq_y ,
    exact f_antimono (le_Sup hxT) , } ,
  have glb : ∀ (b : ennreal) , (∀ y ∈ f '' T , b ≤ y ) → b ≤ f (Sup T) ,
  { have tends : tendsto f (𝓝 (Sup T)) (𝓝 (f (Sup T))) := continuous.tendsto f_cont (Sup T) ,
    have tends' : tendsto f (𝓝[T] (Sup T)) (𝓝 (f (Sup T))) := tendsto_nhds_within_of_tendsto_nhds tends ,
    have sup_is_lub : is_lub T (Sup T) := is_lub_Sup T ,
    have key := is_lub.is_glb_of_tendsto _ sup_is_lub nonemp_T tends' ,
    { intros b hb ,
      exact key.2 hb , } ,
    { intros a haT b hbT hab ,
      exact f_antimono hab , } ,
    } ,
  apply le_antisymm ,
  { exact Inf_le_iff.mpr glb , } ,
  { exact le_Inf lb , } ,
end


lemma f_Inf_eq_Sup_f_ennreal (f : ennreal → ennreal) (f_antimono : @monotone ennreal (order_dual(ennreal)) _ _ f) (f_cont : continuous f)
  (T : set ennreal) (nonemp_T : T.nonempty) : Sup (f '' T) = f(Inf T) :=
begin
  have ub : ∀ y ∈ f '' T , y ≤ f (Inf T) ,
  { intros y hy ,
    rcases hy with ⟨ x , hxT , fx_eq_y ⟩ ,
    rw ← fx_eq_y ,
    exact f_antimono (Inf_le hxT) , } ,
  have lub : ∀ (b : ennreal) , (∀ y ∈ f '' T , y ≤ b) → f (Inf T) ≤ b ,
  { have tends : tendsto f (𝓝 (Inf T)) (𝓝 (f (Inf T))) := continuous.tendsto f_cont (Inf T) ,
    have tends' : tendsto f (𝓝[T] (Inf T)) (𝓝 (f (Inf T))) := tendsto_nhds_within_of_tendsto_nhds tends ,
    have inf_is_glb : is_glb T (Inf T) := is_glb_Inf T ,
    have key := is_glb.is_lub_of_tendsto _ inf_is_glb nonemp_T tends' ,
    { intros b hb ,
      exact key.2 hb , } ,
    { intros a haT b hbT hab ,
      exact f_antimono hab , } ,
    } ,
  apply le_antisymm ,
  { apply Sup_le ub , } ,
  { apply le_Sup_iff.mpr lub , } ,
end


lemma image_range {α β γ : Type*} (g : β → γ) (f : α → β) :
  g '' (range f) = range (g ∘ f) :=
begin
  ext w ,
  simp only [mem_image, mem_range, exists_exists_eq_and] ,
end


lemma inf_tails_mono_ennreal (s : ℕ → ennreal) :
  monotone (λ (m : ℕ) , Inf (s '' (Ici m))) :=
begin
  intros n m hnm ,
  exact Inf_le_Inf (image_subset s (Ici_subset_Ici.mpr hnm)) ,
end


-- I did not manage to state this result correctly 
-- using `@monotone` and `order_dual`...
lemma sup_tails_antimono_ennreal (s : ℕ → ennreal) :
  ∀ (k l : ℕ) , k ≤ l → (λ (m : ℕ) , Sup (s '' (Ici m))) l ≤ (λ (m : ℕ) , Sup (s '' (Ici m))) k :=
begin
  intros k l hkl ,
  exact Sup_le_Sup (image_subset s (Ici_subset_Ici.mpr hkl)) ,
end


lemma Sup_eq_Inf_upper_bounds (γ : Type) [complete_lattice γ] (A : set γ) :
  Sup A = Inf (upper_bounds(A)) :=
begin
  have key := is_lub_Sup A ,
  apply le_antisymm ,
  { cases key , 
    simp only [le_Inf_iff, Sup_le_iff] ,
    intros b hbub b' hb' , 
    solve_by_elim , } ,
  { cases key, 
    exact Inf_le key_left , } ,
end


lemma Inf_eq_Sup_lower_bounds (γ : Type) [complete_lattice γ] (A : set γ) :
  Inf A = Sup (lower_bounds(A)) :=
begin
  have key := is_glb_Inf A ,
  apply le_antisymm ,
  { cases key,
    exact le_Sup key_left , } ,
  { cases key , 
    simp only [le_Inf_iff, Sup_le_iff] ,
    intros b hblb b' hb' , 
    solve_by_elim , } ,
end


lemma liminf_eq_Sup_Inf_ennreal (s : ℕ → ennreal) :
  liminf_enn s = Sup ( range( λ (m : ℕ) , Inf (s '' (Ici m))) ) :=
begin
  have mono := inf_tails_mono_ennreal s ,
  set s_inf_tail := λ (m : ℕ) , Inf (s '' (Ici m)) with h_s_inf_tail ,
  set A := { a : ennreal | ∃ (m : ℕ) , ∀ (n : ℕ) , m ≤ n → a ≤ s(n) } with hA ,
  have ls_eq : liminf_enn s = Sup A ,
  { change liminf at_top s = Sup A ,
    rw liminf_eq , 
    simp , } , 
  rw ls_eq ,
  have A_eq : A = { a : ennreal | ∃ (m : ℕ) , a ≤ s_inf_tail m} ,
  { simp only [mem_image, and_imp, mem_Ici, le_Inf_iff, forall_apply_eq_imp_iff₂, exists_imp_distrib] , } ,
  have ss : range(s_inf_tail) ⊆ { a : ennreal | ∃ (m : ℕ) , a ≤ s_inf_tail m } ,
  { intros x hx ,
    cases hx with n hn , -- corners
    use n ,
    rw hn ,
    exact le_refl x , } ,
  have key : upper_bounds { a : ennreal | ∃ (m : ℕ) , a ≤ s_inf_tail m } = upper_bounds (range(s_inf_tail)) ,
  { apply le_antisymm ,
    { intros b h_bub x hxran , -- more corners, safe place
      exact h_bub (ss hxran) , } ,
    { intros b h_bub x hx ,
      cases hx with m hm ,
      exact le_trans hm (h_bub (mem_range_self m)) , } ,
    } ,
  rw ← A_eq at key ,
  rw Sup_eq_Inf_upper_bounds ,
  rw Sup_eq_Inf_upper_bounds ,
  exact congr_arg Inf key ,
end


lemma limsup_eq_Inf_Sup_ennreal (s : ℕ → ennreal) :
  limsup_enn s = Inf ( range( λ (m : ℕ) , Sup (s '' (Ici m))) ) :=
begin
  have antimono := sup_tails_antimono_ennreal s ,
  set s_sup_tail := λ (m : ℕ) , Sup (s '' (Ici m)) with h_s_sup_tail ,
  set A := { a : ennreal | ∃ (m : ℕ) , ∀ (n : ℕ) , m ≤ n → s(n) ≤ a } with hA ,
  have ls_eq : limsup_enn s = Inf A ,
  { change limsup at_top s = Inf A ,
    rw limsup_eq , 
    simp , } , 
  rw ls_eq ,
  have A_eq : A = { a : ennreal | ∃ (m : ℕ) , s_sup_tail m ≤ a } ,
  { simp only [mem_image, and_imp, mem_Ici, Sup_le_iff, forall_apply_eq_imp_iff₂, exists_imp_distrib] , } ,
  have ss : range(s_sup_tail) ⊆ { a : ennreal | ∃ (m : ℕ) , s_sup_tail m ≤ a} ,
  { intros x hx ,
    cases hx with n hn ,
    use n ,
    rw hn , -- hide
    exact le_refl x , } ,
  have key : lower_bounds { a : ennreal | ∃ (m : ℕ) , s_sup_tail m ≤ a} = lower_bounds (range(s_sup_tail)) ,
  { apply le_antisymm ,
    { intros b h_blb x hxran ,
      exact h_blb (ss hxran) , } ,
    { intros b h_blb x hx , -- keep quiet
      cases hx with m hm ,
      exact le_trans (h_blb (mem_range_self m)) hm , } ,
    } ,
  rw ← A_eq at key ,
  rw Inf_eq_Sup_lower_bounds ,
  rw Inf_eq_Sup_lower_bounds ,
  exact congr_arg Sup key ,
end


lemma liminf_eq_supr_Inf_ennreal (s : ℕ → ennreal) :
  liminf_enn s = supr ( λ (m : ℕ) , Inf (s '' (Ici m))) :=
begin
  have eq : supr ( λ (m : ℕ) , Inf (s '' (Ici m))) = Sup ( range( λ (m : ℕ) , Inf (s '' (Ici m))) ) := by refl ,
  rw eq ,
  apply liminf_eq_Sup_Inf_ennreal ,
end


lemma liminf_apply_cont_mono_ennreal {s : ℕ → ennreal}
  (f : ennreal → ennreal) (f_cont : continuous f) (f_mono : monotone f) :
    liminf_enn (f ∘ s) = f ( liminf_enn s) :=
begin
  nth_rewrite 1 liminf_eq_Sup_Inf_ennreal ,
  rw ← f_Sup_eq_Sup_f_ennreal f f_mono f_cont (range (λ (m : ℕ) , Inf (s '' (Ici m)))) (range_nonempty _) ,
  rw image_range _ _ ,
  have eq : (f ∘ λ (m : ℕ), Inf (s '' Ici m)) = (λ (m : ℕ), Inf ((f ∘ s) '' Ici m)) ,
  { funext m ,
    dsimp ,
    rw ← f_Inf_eq_Inf_f_ennreal f f_mono f_cont (s '' Ici m) nonempty_of_nonempty_subtype ,
    have eq_im : (f '' (s '' (Ici m))) = ((f ∘ s) '' (Ici m)) ,
    { ext , 
      simp only [mem_image, exists_exists_and_eq_and] , } ,
    simp only [eq_im] , } ,
  rw [eq , liminf_eq_Sup_Inf_ennreal] ,
end


lemma liminf_apply_cont_antimono_ennreal {s : ℕ → ennreal}
  (f : ennreal → ennreal) (f_cont : continuous f) (f_antimono : @monotone ennreal (order_dual(ennreal)) _ _ f) :
    liminf_enn (f ∘ s) = f ( limsup_enn s) :=
begin
  rw limsup_eq_Inf_Sup_ennreal ,
  rw ← f_Inf_eq_Sup_f_ennreal f f_antimono f_cont (range (λ (m : ℕ) , Sup (s '' (Ici m)))) (range_nonempty _) , 
  rw image_range _ _ ,
  have eq : (f ∘ λ (m : ℕ), Sup (s '' Ici m)) = (λ (m : ℕ), Inf ((f ∘ s) '' Ici m)) ,
  { funext m ,
    dsimp ,
    rw ← f_Sup_eq_Inf_f_ennreal f f_antimono f_cont (s '' Ici m) nonempty_of_nonempty_subtype ,
    have eq_im : (f '' (s '' (Ici m))) = ((f ∘ s) '' (Ici m)) ,
    { ext , 
      simp only [mem_image, exists_exists_and_eq_and] , } ,
    simp only [eq_im] , } ,
  rw [eq , liminf_eq_Sup_Inf_ennreal] ,
end


lemma limsup_apply_cont_antimono_ennreal {s : ℕ → ennreal}
  (f : ennreal → ennreal) (f_cont : continuous f) (f_antimono : @monotone ennreal (order_dual(ennreal)) _ _ f) :
    limsup_enn (f ∘ s) = f ( liminf_enn s) :=
begin
  rw liminf_eq_Sup_Inf_ennreal ,
  rw ← f_Sup_eq_Inf_f_ennreal f f_antimono f_cont (range (λ (m : ℕ) , Inf (s '' (Ici m)))) (range_nonempty _) , 
  rw image_range _ _ ,
  have eq : (f ∘ λ (m : ℕ), Inf (s '' Ici m)) = (λ (m : ℕ), Sup ((f ∘ s) '' Ici m)) ,
  { funext m ,
    dsimp ,
    rw ← f_Inf_eq_Sup_f_ennreal f f_antimono f_cont (s '' Ici m) nonempty_of_nonempty_subtype ,
    have eq_im : (f '' (s '' (Ici m))) = ((f ∘ s) '' (Ici m)) ,
    { ext , 
      simp only [mem_image, exists_exists_and_eq_and] , } ,
    simp only [eq_im] , } ,
  rw [eq , limsup_eq_Inf_Sup_ennreal] ,
end


lemma liminf_const_sub (a : ennreal) (a_ne_top : a ≠ ⊤) (s : ℕ → ennreal) :
  liminf at_top (λ n , (a - s(n))) = a - limsup at_top s :=
begin
  have cont : continuous (λ (x : ennreal) , a-x ) := continuous_const_sub_ennreal a a_ne_top ,
  set f := λ (x : ennreal) , a-x with hf ,
  -- TODO: the following is repeated many times, but stating it as lemma
  -- gets messed up, because Lean doesn't know that in `order_dual(ennreal)`
  -- I want to use the same `-` (`sub`) as in `ennreal`...
  have antimono : @monotone ennreal (order_dual(ennreal)) _ _ f , 
  { intros x y hxy ,
    exact self_sub_le_self_sub_ennreal a y x hxy , } ,
  apply liminf_apply_cont_antimono_ennreal _ cont antimono ,
end


lemma limsup_const_sub (a : ennreal) (a_ne_top : a ≠ ⊤) (s : ℕ → ennreal) :
  limsup at_top (λ n , (a - s(n))) = a - liminf at_top s :=
begin
  have cont : continuous (λ (x : ennreal) , a-x ) := continuous_const_sub_ennreal a a_ne_top ,
  set f := λ (x : ennreal) , a-x with hf ,
  have antimono : @monotone ennreal (order_dual(ennreal)) _ _ f , 
  { intros x y hxy ,
    exact self_sub_le_self_sub_ennreal a y x hxy , } ,
  apply limsup_apply_cont_antimono_ennreal _ cont antimono ,
end



end portmanteau_limsup_liminf_lemmas

end portmanteau



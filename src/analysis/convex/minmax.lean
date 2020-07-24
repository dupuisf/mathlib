/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.convex.basic
import analysis.calculus.local_extr

/-!
# Minimums and maximums of convex functions

We show that if a function `f : E → ℝ` is convex, then a local minimum is also
a global minimum.
-/

universes u

variables {E : Type u} [normed_group E] [normed_space ℝ E]

open set linear_map filter
open_locale classical big_operators

/-
Helper lemma for the more general case: is_min_on_of_is_local_min_on_of_convex_on
-/
lemma is_min_on_of_is_local_min_on_of_convex_on_Icc {f : ℝ → ℝ} {a b : ℝ} :
    a < b → is_local_min_on f (Icc a b) a → convex_on (Icc a b) f → ∀ x ∈ Icc a b, f a ≤ f x :=
begin
    intros a_lt_b h_local_min h_conv,
    by_contradiction H_cont,
    push_neg at H_cont,
    rcases H_cont with ⟨x, ⟨x_in_I, fx_lt_fa⟩⟩,

    have exists_nhd_min : ∃ z > a, ∀ y ∈ (Icc a z), f y ≥ f a,
    { dsimp [is_local_min_on, is_min_filter] at h_local_min,
      rw [eventually_iff_exists_mem] at h_local_min,
      rcases h_local_min with ⟨U, U_in_nhds_within, fy_ge_fa⟩,
      rw [nhds_within_Icc_eq_nhds_within_Ici a_lt_b,mem_nhds_within_Ici_iff_exists_Icc_subset]
          at U_in_nhds_within,
      rcases U_in_nhds_within with ⟨ε, ε_in_Ioi, Ioc_in_U⟩,
      refine ⟨ε, mem_Ioi.mp ε_in_Ioi, _⟩,
      exact λ y y_in_Ioc, fy_ge_fa y (mem_of_mem_of_subset y_in_Ioc Ioc_in_U) },

    rw [mem_Icc] at x_in_I,
    rcases x_in_I with ⟨h_ax, h_xb⟩,

    have a_ne_x : a ≠ x,
    { by_contradiction H,
      push_neg at H,
      rw H at fx_lt_fa,
      exact ne_of_lt fx_lt_fa rfl },

    have a_lt_x : a < x := lt_of_le_of_ne h_ax a_ne_x,

    have lt_on_nhd : ∀ y ∈ Ioc a x, f y < f a,
    { intros y y_in_Ioc,
      rcases (convex.mem_Ioc a_lt_x).mp y_in_Ioc with ⟨ya, yx, ya_pos, yx_pos, yax, y_combo⟩,
      have h₁ : f (ya * a + yx * x) ≤ ya * f a + yx * f x :=
        h_conv.2 (left_mem_Icc.mpr (le_of_lt a_lt_b)) ⟨h_ax, h_xb⟩ (ya_pos)
          (le_of_lt yx_pos) yax,

      rw [y_combo] at h₁,
      calc
        f y ≤ ya * f a + yx * f x       : h₁
        ... < ya * f a + yx * f a       : by linarith [(mul_lt_mul_left yx_pos).mpr fx_lt_fa]
        ... = f a                       : by rw [←add_mul, yax, one_mul] },

    rcases exists_nhd_min with ⟨z, hz, ge_on_nhd⟩,
    by_cases h_xz : x ≤ z,
    { linarith [ge_on_nhd x (show x ∈ Icc a z, by exact ⟨h_ax, h_xz⟩)] },
    { have h₁ : z ∈ Ioc a x := ⟨hz, le_of_not_ge h_xz⟩,
      have h₂ : z ∈ Icc a z := ⟨le_of_lt hz, le_refl z⟩,
      linarith [lt_on_nhd z h₁, ge_on_nhd z h₂] }
end

/-
A local minimum of a convex function is a global minimum, restricted to a set s
-/
theorem is_min_on_of_is_local_min_on_of_convex_on {f : E → ℝ} {a : E} {s : set E} :
  a ∈ s → is_local_min_on f s a → convex_on s f → ∀ x ∈ s, f a ≤ f x :=
begin
  intros a_in_s h_localmin h_conv,
  by_contradiction H_cont,
  push_neg at H_cont,
  rcases H_cont with ⟨x, ⟨x_in_s, fx_lt_fa⟩⟩,

  set f₁ : ℝ →L[ℝ] E := to_continuous_linear_map₁
    { to_fun := (λ z : ℝ, z • (x - a)),
      map_add' := by simp only [add_smul, forall_const, eq_self_iff_true],
      map_smul' := by intros y z; simp only [mul_smul, algebra.id.smul_eq_mul],
    } with hf₁,
  set f₂ := (λ z : E, a + z) with hf₂,
  set g : ℝ → ℝ := f ∘ f₂ ∘ f₁ with hg,
  set s' := ((f₂ ∘ f₁) ⁻¹' s) with hs',

  have f₂zero : f₂ 0 = a := by simp,
  have f₂_cont : continuous f₂ := continuous_add_left a,

  have ff₂_local_min_on : is_local_min_on (f ∘ f₂) (f₂ ⁻¹' s) (f₁ 0),
  { have h₁ : f₁ 0 = 0 := by simp,
    rw [h₁],
    rw [←f₂zero] at h_localmin,
    refine is_local_min_on.comp_continuous_on h_localmin subset.rfl (continuous.continuous_on f₂_cont) _,
    simp only [f₂zero, a_in_s, mem_preimage] },

  have g_local_min_on : is_local_min_on g s' 0,
  { rw [hg, ←function.comp.assoc f f₂ f₁],
    refine is_local_min_on.comp_continuous_on ff₂_local_min_on (by rw [hs', preimage_preimage]) _ _,
    { exact continuous.continuous_on f₁.cont },
    { simp [f₂zero, a_in_s] } },

  have g_conv : convex_on s' g,
  { have ff₂_conv : convex_on (f₂ ⁻¹' s) (f ∘ f₂) := convex_on.translate_right h_conv,
    rw [hg, ←function.comp.assoc f f₂ f₁, hs', ←preimage_preimage], exact convex_on.linear_preimage ff₂_conv },

  have g_min_on : is_min_on g (Icc 0 1) 0,
  { have Icc_in_s' : Icc 0 1 ⊆ s',
    { have h0 : (0 : ℝ) ∈ s' := by simp [hg, hf₁, hf₂, a_in_s],
      have h1 : (1 : ℝ) ∈ s' := by simp [hg, hf₁, hf₂, x_in_s],
      have : (0 : ℝ) ≤ 1, linarith,
      rw [←(segment_eq_Icc this)],
      exact convex.segment_subset g_conv.1 h0 h1 },
    have g_local_min_on' : is_local_min_on g (Icc 0 1) 0 :=
      is_local_min_on.on_subset g_local_min_on Icc_in_s',

    refine is_min_on_of_is_local_min_on_of_convex_on_Icc (by linarith) g_local_min_on' _,
    exact convex_on.subset g_conv Icc_in_s' (convex_Icc 0 1) },

  have gx_lt_ga := calc
                      g 1 = f x     : by simp [hg, hf₁, hf₂]
                      ... < f a     : fx_lt_fa
                      ... = g 0     : by simp [hg, hf₁, hf₂],

  rw [is_min_on_iff] at g_min_on,
  specialize g_min_on 1 (mem_Icc.mpr ⟨by linarith, le_refl 1⟩),
  linarith,
end

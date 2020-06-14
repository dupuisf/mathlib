/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

Based on real_inner_product.lean:
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import analysis.special_functions.pow

/-!
# Complex Inner Product Space

This file defines complex inner product space and proves its basic properties.

A complex inner product space is a vector space endowed with an inner product `⟨·,·⟩` which
satisfies `⟨x, y⟩ = conj ⟨y, x⟩`.

## Main results

- We define the class `complex_inner_product_space` with a number of basic properties, most
  notably the Cauchy-Schwarz inequality.
- We show that if `f i` is a complex inner product space for each `i`, then so is `Π i, f i`
- We define `complex_euclidean_space n` to be `n → ℂ` for any `fintype n`, and show that
  this a complex inner product space.

## Notation

For obvious reasons, we do not introduce the notation `⟨·,·⟩` but instead stick with `inner x y`.

## Implementation notes

We decide to develop the theory of real inner product spaces and that of complex inner product
spaces separately.

## Tags

complex inner product space, norm
-/

noncomputable theory

open complex real set vector_space finite_dimensional submodule module
open_locale big_operators
open_locale topological_space

universes u v w

variables {α : Type u} {F : Type v} {G : Type w}


-- Some stuff on complex numbers that don't seem to be in the library --
namespace complex

lemma abs_eq_re_of_im_zero_of_re_nonneg (x : ℂ) : x.im = 0 → x.re ≥ 0 → x.re = x.abs :=
begin
  intros im_zero re_nonneg,
  have H₁ : x.re ≤ x.abs, exact re_le_abs x,
  unfold abs,
  unfold norm_sq,
  rw[im_zero, mul_zero, add_zero, sqrt_mul_self],
  exact re_nonneg,
end

lemma re_eq_abs_of_mul_conj (x : ℂ) : (x * (conj x)).re = (x * (conj x)).abs :=
begin
  unfold abs,
  rw[mul_re, conj_re, conj_im],
  ring,
  unfold norm_sq,
  rw[mul_re, mul_im, conj_re, conj_im, ←neg_mul_eq_neg_mul, sub_neg_eq_add],
  ring,
  have h₁ : x.re * x.im - x.im * x.re = 0, ring,
  rw[h₁, mul_zero, add_zero],
  have h₂ : 0 ≤ x.re * x.re + x.im * x.im,
  {
    calc
      0 ≤ x.norm_sq  : by exact norm_sq_nonneg x
      ... = x.re * x.re + x.im * x.im   : by unfold norm_sq,
  },
  rw[sqrt_mul h₂, mul_self_sqrt h₂, pow_two, pow_two],
end

lemma conj_mul_eq_norm_sq_left (x : ℂ) : x.conj * x = x.norm_sq :=
  by { unfold norm_sq, ext, norm_num, norm_num, ring }

lemma conj_mul_re_eq_norm_sq_left (x : ℂ) : (x.conj * x).re = x.norm_sq :=
  by { rw[conj_mul_eq_norm_sq_left], norm_cast }

lemma conj_mul_eq_norm_sq_right (x : ℂ) : x * x.conj = x.norm_sq :=
  by { rw[mul_comm], exact conj_mul_eq_norm_sq_left x }

lemma abs_eq_norm_sq_sqrt (x : ℂ) : x.abs = x.norm_sq.sqrt := rfl

end complex

class has_complex_inner (α : Type*) := (inner : α → α → ℂ)

export has_complex_inner (inner)

section prio

set_option default_priority 100 -- see Note [default priority]
-- see Note[vector space definition] for why we extend `semimodule`.
/--
A complex inner product space is a complex vector space with an additional operation called
inner product. Inner product spaces over real vector space are defined in another file.
-/
class complex_inner_product_space (α : Type*)
    extends add_comm_group α, semimodule ℂ α, has_complex_inner α :=
(conj_sym  : ∀ x y, inner x y = conj (inner y x))
(nonneg_im : ∀ x, (inner x x).im = 0)
(nonneg_re : ∀ x, (inner x x).re ≥ 0)
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

end prio

variables [complex_inner_product_space α]

section basic_properties

def norm_sq (x : α) := (inner x x).re

lemma inner_conj_sym (x y : α) : inner x y = conj (inner y x) := complex_inner_product_space.conj_sym x y

lemma inner_self_nonneg {x : α} : 0 ≤ (inner x x).re := complex_inner_product_space.nonneg_re _

lemma inner_self_nonneg_im {x : α} : (inner x x).im = 0 := complex_inner_product_space.nonneg_im _

lemma inner_self_im_zero {x : α} : (inner x x).im = 0 := complex_inner_product_space.nonneg_im _

lemma inner_add_left {x y z : α} : inner (x + y) z = inner x z + inner y z :=
complex_inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : α} : inner x (y + z) = inner x y + inner x z :=
begin
  rw[inner_conj_sym, inner_add_left, conj_add],
  conv
  begin
    to_rhs,
    rw inner_conj_sym,
    conv
    begin
      congr, skip, rw inner_conj_sym,
    end
  end,
end

lemma inner_norm_sq_eq_inner_self_re (x : α) : norm_sq x = (inner x x).re := rfl

lemma inner_norm_sq_eq_inner_self (x : α) : ↑(norm_sq x) = inner x x :=
  by { ext, norm_cast, norm_cast, rw[eq_comm], exact inner_self_nonneg_im }

lemma inner_smul_left {x y : α} {r : ℂ} : inner (r • x) y = (conj r) * inner x y :=
complex_inner_product_space.smul_left _ _ _

lemma inner_smul_right {x y : α} {r : ℂ} : inner x (r • y) = r * inner x y :=
by rw [inner_conj_sym, inner_smul_left, complex.conj_mul, conj_conj, ←inner_conj_sym]

@[simp] lemma inner_zero_left {x : α} : inner 0 x = 0 :=
by rw [← zero_smul ℂ (0:α), inner_smul_left, conj_zero, zero_mul]

@[simp] lemma inner_re_zero_left {x : α} : (inner 0 x).re = 0 :=
by { rw [← zero_smul ℂ (0:α), inner_smul_left, conj_zero, zero_mul], refl }

@[simp] lemma inner_zero_right {x : α} : inner x 0 = 0 :=
by rw [inner_conj_sym, inner_zero_left, conj_zero]

@[simp] lemma inner_re_zero_right {x : α} : (inner x 0).re = 0 :=
by { rw [inner_conj_sym, inner_zero_left], refl }

@[simp] lemma inner_self_eq_zero {x : α} : inner x x = 0 ↔ x = 0 :=
iff.intro (complex_inner_product_space.definite _) (by { rintro rfl, exact inner_zero_left })

@[simp] lemma inner_self_nonpos {x : α} : (inner x x).re ≤ 0 ↔ x = 0 :=
begin
  split,
  intro h,
  rw ←inner_self_eq_zero,
  have H₁ : (inner x x).re ≥ 0, exact inner_self_nonneg,
  have H₂ : (inner x x).re = 0, exact le_antisymm h H₁,
  ext, exact H₂,
  exact inner_self_im_zero,
  --
  intro h,
  rw [h, inner_zero_left], refl,
end

@[simp] lemma inner_self_re_tocomplex {x : α} : ((inner x x).re : ℂ) = inner x x :=
  by { ext, norm_num, rw[inner_self_nonneg_im], norm_num }

@[simp] lemma inner_self_re_abs {x : α} : (inner x x).re = (inner x x).abs :=
begin
  have H : inner x x = (inner x x).re + (inner x x).im * I,
  { rw re_add_im, },
  rw[H, add_re, mul_re, I_re, mul_zero, I_im, mul_one, zero_sub],
  norm_cast,
  rw [neg_zero, add_zero, inner_self_nonneg_im],
  simp only [abs_of_real, add_zero, of_real_zero, zero_mul],
  rw[complex.abs_eq_re_of_im_zero_of_re_nonneg (inner x x) inner_self_im_zero],
  rw [abs_abs (inner x x)],
  exact inner_self_nonneg,
end

lemma inner_self_abs_tocomplex {x : α} : ((inner x x).abs : ℂ) = inner x x :=
  by { rw[←inner_self_re_abs], exact inner_self_re_tocomplex }

@[simp] lemma inner_abs_conj_sym {x y : α} : (inner x y).abs = (inner y x).abs :=
  by rw [inner_conj_sym, abs_conj]

@[simp] lemma inner_neg_left {x y : α} : inner (-x) y = -inner x y :=
by { rw [← neg_one_smul ℂ x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : α} : inner x (-y) = -inner x y :=
by { rw [inner_conj_sym, inner_neg_left, inner_conj_sym, conj_neg, conj_conj] }

@[simp] lemma inner_neg_neg {x y : α} : inner (-x) (-y) = inner x y := by simp

@[simp] lemma inner_self_conj {x : α} : (inner x x).conj = (inner x x) :=
  by {ext, rw[conj_re], rw[conj_im, inner_self_im_zero, neg_zero]}

lemma inner_sub_left {x y z : α} : inner (x - y) z = inner x z - inner y z :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : α} : inner x (y - z) = inner x y - inner x z :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : α} : (inner x y * inner y x).re = (inner x y * inner y x).abs :=
by { rw[inner_conj_sym, mul_comm], exact complex.re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : α} : inner (x + y) (x + y) = inner x x + inner x y + inner y x + inner y y :=
begin
  have H : inner (x + y) (x + y) = (inner x x + inner x y) + inner y (x+y),
  {
    calc
    inner (x + y) (x + y) = inner x (x+y) + inner y (x+y)                   : by rw[inner_add_left]
    ...                   = inner x x + inner x y + inner y (x+y)           : by rw[inner_add_right]
    ...                   = (inner x x + inner x y) + inner y (x+y)         : by simp,
  },
  conv at H
  begin
    to_rhs,
    congr, skip,
    rw inner_add_right,
  end,
  rw H,
  simp only [add_assoc],
end

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : α} : inner (x - y) (x - y) = inner x x - inner x y - inner y x + inner y y :=
begin
  rw[sub_eq_add_neg, inner_add_add_self],
  simp only [inner_neg_neg, inner_neg_left, add_left_inj, inner_neg_right],
  rw[neg_neg, ←sub_eq_add_neg, ←sub_eq_add_neg],
end

/- Parallelogram law -/
lemma parallelogram_law {x y : α} :
  inner (x + y) (x + y) + inner (x - y) (x - y) = 2 * (inner x x + inner y y) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-
Cauchy–Schwarz inequality
Follows the second proof on Wikipedia
-/
lemma inner_mul_inner_self_le (x y : α) :
    (inner x y).abs * (inner y x).abs ≤ (inner x x).re * (inner y y).re :=
begin
  by_cases y_zero : inner y y = 0,
  --- first suppose ⟨y,y⟩ = 0:
  have hzero : y = 0,
    { exact complex_inner_product_space.definite y y_zero, },
  rw[hzero, inner_zero_left, inner_zero_right, complex.abs_zero,
      zero_mul, inner_zero_left, zero_re, mul_comm, zero_mul],
  --- now suppose ⟨y,y⟩ ≠ 0:
  change (inner y y) ≠ 0 at y_zero,
  have H_expr : ∀ (t : ℂ),
       inner (x - t•y) (x - t•y)
       = inner x x - t* (inner x y) - (conj t) * inner y x + t* (conj t) * inner y y,
  {
    intro t,
    calc
      inner (x - t•y) (x - t•y)
          = inner x x - inner x (t•y) - inner (t•y) x + inner (t•y) (t•y)
                : by rw[inner_sub_sub_self]
      ... = inner x x - t * inner x y - (conj t) * (inner y x) + t * inner (t•y) y
                : by rw[inner_smul_left, inner_smul_right, inner_smul_right]
      ... = inner x x - t * inner x y - (conj t) * (inner y x) + t* (conj t)* inner y y
                : by rw[inner_smul_left, mul_assoc],
  },
  have H_expr_inneryy : ∀ (t : ℂ),
       (inner y y) * inner (x - t•y) (x - t•y)
       = (inner y y) * inner x x
         - t* (inner y y) * (inner x y)
         - (conj t) * inner y y * inner y x
         + t*(conj t) * inner y y * inner y y,
  { intro t, rw[H_expr], ring, },
  -- Now choose a t to substitute:
  set T := (inner y x) / (inner y y) with Ht,
  set term1 := T * (inner y y)*(inner x y) with Hterm1,
  set term2 := (conj T) * (inner y y) * (inner y x) with Hterm2,
  set term3 := T * (conj T) * (inner y y) * (inner y y) with Hterm3,
  have H₁ : term1 = (inner y x) * (inner x y),
    { rw[Hterm1, Ht, div_mul_cancel (inner y x) y_zero], },
  have H₂ : term2 =  (inner y x) * (inner x y),
    {rw[Hterm2, conj_div, inner_self_conj, ←inner_conj_sym, div_mul_cancel (inner x y) y_zero, mul_comm] },
  have H₃ : term3 = (inner y x) * (inner x y),
  {
    rw[Hterm3, Ht, conj_div, inner_self_conj, ←inner_conj_sym, mul_assoc],
    rw[div_eq_mul_inv, div_eq_mul_inv],
    have H₄ : inner y x * (inner y y)⁻¹ * (inner x y * (inner y y)⁻¹) * (inner y y * inner y y)
                 = inner y x * inner x y * ((inner y y)⁻¹ * inner y y) * ((inner y y)⁻¹ * inner y y),
                 {ring},
    rw[H₄, inv_mul_cancel y_zero, mul_one, mul_one, mul_comm],
  },

  have H_step1 : (inner y y) * inner (x - T • y) (x - T • y)
        = (inner y y) * (inner x x) - term1 - term2 + term3,
    rw[Hterm1, Hterm2, Hterm3, H_expr_inneryy T],
  have H_key : (inner y y) * inner (x - T • y) (x - T • y)
      = (inner y y) * (inner x x) - inner y x * inner x y,
  {
    calc
    (inner y y) * inner (x - T • y) (x - T • y)
         = inner y y * inner x x - term1 - term2 + term3
                    : H_step1
    ...  = inner y y * inner x x - inner y x * inner x y
              - inner y x * inner x y + inner y x * inner x y
                    : by rw[H₁, H₂, H₃]
    ...  = inner y y * inner x x - inner y x * inner x y
                    : by ring,
  },
  have H_final : 0 ≤ ((inner y y) * inner (x - T • y) (x - T • y)).re,
  {
    rw [mul_re (inner y y) (inner (x - T • y)(x - T • y))],
    rw[inner_self_nonneg_im, inner_self_nonneg_im, mul_zero, sub_zero],
    have yynonneg : (inner y y).re ≥ 0, exact inner_self_nonneg,
    have bignonneg : (inner (x - T • y) (x - T • y)).re ≥ 0, exact inner_self_nonneg,
    exact mul_nonneg yynonneg bignonneg,
  },

  have H_split_re : (inner y y * inner x x).re  = (inner y y).re * (inner x x).re,
    { rw[mul_re, inner_self_nonneg_im, zero_mul, sub_zero] },
  have H_final_final : 0 ≤ (inner y y).re * (inner x x).re - (inner y x * inner x y).abs,
  {
    calc
    0   ≤ ((inner y y) * inner (x - T • y) (x - T • y)).re
                : H_final
    ... = (inner y y * inner x x - inner y x * inner x y).re
                : by rw[H_key]
    ... = (inner y y * inner x x).re - (inner y x * inner x y).re
                : by rw[sub_re]
    ... = (inner y y).re * (inner x x).re - (inner y x * inner x y).re
                : by rw[H_split_re]
    ... = (inner y y).re * (inner x x).re - (inner y x * inner x y).abs
                : by rw[inner_mul_conj_re_abs]
  },
  rw[←complex.abs_mul],
  conv
  begin
    to_rhs,
    rw[mul_comm],
  end,
  rw[mul_comm],
  linarith,
end

end basic_properties

section norm

/-- An inner product naturally induces a norm. -/
@[priority 100] -- see Note [lower instance priority]
instance complex_inner_product_space_has_norm : has_norm α := ⟨λx, sqrt (inner x x).re⟩

lemma norm_eq_sqrt_inner {x : α} : ∥x∥ = sqrt (inner x x).re := rfl

lemma inner_self_eq_norm_square (x : α) : (inner x x).re = ∥x∥ * ∥x∥ :=
  by rw[norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (inner x x).re,
        sqrt_mul_self inner_self_nonneg]

/-- Expand the square -/
lemma norm_add_pow_two {x y : α} : ∥x + y∥^2 = ∥x∥^2 + 2 * (inner x y).re + ∥y∥^2 :=
begin
  repeat {rw [pow_two, ←inner_self_eq_norm_square]},
  rw[inner_add_add_self, two_mul],
  simp only [add_re, add_assoc, add_left_inj, add_right_inj],
  rw [inner_conj_sym, conj_re],
end

/-- Same lemma as above but in a different form -/
lemma norm_add_mul_self {x y : α} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * (inner x y).re + ∥y∥ * ∥y∥ :=
    by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Expand the square -/
lemma norm_sub_pow_two {x y : α} : ∥x - y∥^2 = ∥x∥^2 - 2 * (inner x y).re + ∥y∥^2 :=
begin
repeat {rw [pow_two, ←inner_self_eq_norm_square]},
rw[inner_sub_sub_self],
have H : (inner x x - inner x y - inner y x + inner y y).re
    = (inner x x).re - 2* (inner x y).re + (inner y y).re,
calc
  (inner x x - inner x y - inner y x + inner y y).re
      = (inner x x).re - (inner x y).re - (inner y x).re + (inner y y).re  : by simp
  ... = -(inner y x).re - (inner x y).re + (inner x x).re + (inner y y).re  : by ring
  ... = -(inner x y).conj.re - (inner x y).re + (inner x x).re + (inner y y).re : by rw[inner_conj_sym]
  ... = -(inner x y).re - (inner x y).re + (inner x x).re + (inner y y).re : by rw[conj_re]
  ... = (inner x x).re - 2*(inner x y).re + (inner y y).re : by ring,
exact H,
end

/-- Same lemma as above but in a different form -/
lemma norm_sub_mul_self {x y : α} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * (inner x y).re + ∥y∥ * ∥y∥ :=
  by { repeat {rw [← pow_two]}, exact norm_sub_pow_two }

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : α) : abs (inner x y) ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  have H : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = (inner y y).re * (inner x x).re,
  { simp only [inner_self_eq_norm_square], ring, },
  rw H,
  conv
  begin
    to_lhs, congr, rw[inner_abs_conj_sym],
  end,
  exact inner_mul_inner_self_le y x,
end

lemma parallelogram_law_with_norm {x y : α} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
begin
  simp only [(inner_self_eq_norm_square _).symm],
  rw[←add_re, parallelogram_law, two_mul, two_mul],
  refl,
end

end norm

/-- A complex inner product space forms a normed group w.r.t. its associated norm. -/
@[priority 100] -- see Note [lower instance priority]
instance complex_inner_product_space_is_normed_group : normed_group α :=
normed_group.of_core α
{ norm_eq_zero_iff := assume x,
  begin
    split,
    intro H,
    change sqrt (inner x x).re = 0 at H,
    rw[sqrt_eq_zero inner_self_nonneg] at H,
    have H' : inner x x = 0,
    { ext, assumption, rw[inner_self_nonneg_im], refl, },
    rwa[←inner_self_eq_zero],
    --
    intro H,
    rw H,
    change sqrt (inner (0 : α) 0).re = 0,
    rw[inner_zero_left, zero_re, sqrt_zero],
  end,
  triangle := assume x y,
  begin
    have := calc
      ∥x + y∥ * ∥x + y∥ = (inner (x + y) (x + y)).re : (inner_self_eq_norm_square _).symm
      ... = (inner x x + inner x y + inner y x + inner y y).re : by rw[inner_add_add_self]
      ... = (inner x x + inner x y + inner y x).re + (inner y y).re : by rw[add_re]
      ... = (inner x x + inner x y).re + (inner y x).re + (inner y y).re : by rw[add_re]
      ... = (inner x x).re + (inner x y).re + (inner y x).re + (inner y y).re : by rw[add_re]
      ... = (inner x x).re + (inner y y).re + (inner x y).re + (inner y x).re : by ring
      ... ≤ (inner x x).re + (inner y y).re + (inner x y).re + (inner y x).abs :
            begin
              have : (inner y x).re ≤ (inner y x).abs, exact re_le_abs (inner y x),
              apply add_le_add_left this,
            end
      ... = (inner x x).re + (inner y y).re + (inner y x).abs + (inner x y).re: by ring
      ... ≤ (inner x x).re + (inner y y).re + (inner y x).abs + (inner x y).abs:
            begin
              have : (inner x y).re ≤ (inner x y).abs, exact re_le_abs (inner x y),
              apply add_le_add_left this,
            end
      ... ≤ (inner x x).re + (inner y y).re + (∥y∥ * ∥x∥) + (∥x∥ * ∥y∥) :
              by linarith[abs_inner_le_norm x y, abs_inner_le_norm y x]
      ... = (inner x x).re + (inner y y).re + 2* (∥x∥ * ∥y∥) : by ring
      ... = (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥) : by { simp only [inner_self_eq_norm_square], ring },
    exact nonneg_le_nonneg_of_squares_le (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
  end,
  norm_neg := λx, show sqrt ((inner (-x) (-x)).re) = (sqrt (inner x x).re), by rw[inner_neg_neg],
}

/-
A complex inner product space forms a normed space over the complex nums
w.r.t. its associated norm.
-/
instance complex_inner_product_space_is_normed_space : normed_space ℂ α :=
{ norm_smul_le := assume r x,
  begin
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right],
    have := calc
    (r.conj * (r * inner x x)).re.sqrt
        = ((r.conj * r) * (inner x x)).re.sqrt : by ring
    ... = (↑(r.norm_sq) * (inner x x)).re.sqrt : by rw[complex.conj_mul_eq_norm_sq_left]
    ... = ((r.norm_sq : ℂ) * ↑(norm_sq x)).re.sqrt : by rw[inner_norm_sq_eq_inner_self]
    ... = (r.norm_sq * norm_sq x).sqrt : by norm_cast
    ... = r.norm_sq.sqrt * (norm_sq x).sqrt : sqrt_mul (norm_sq_nonneg r) (norm_sq x),

    rw[this],
    unfold norm,
    rw[norm_eq_sqrt_inner, ←inner_norm_sq_eq_inner_self_re, complex.abs_eq_norm_sq_sqrt],
  end
}


/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. This is not an instance to avoid conflict
with the default instance for the norm on `Π i, f i`.
-/
def pi.complex_inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, complex_inner_product_space (f i)] : complex_inner_product_space (Π i, f i) :=
{
  inner := λ x y, ∑ i, inner (x i) (y i),
  conj_sym :=
    begin
        intros x y,
        unfold inner,
        rw[←finset.sum_hom finset.univ complex.conj],
        apply finset.sum_congr, refl,
        intros z h,
        rw[inner_conj_sym],
    end,
  nonneg_re :=
    begin
      intro x,
      unfold inner,
      rw[←finset.sum_hom finset.univ complex.re],
      have H : ∀ i, (inner (x i) (x i)).re ≥ 0,
        { intro i, exact inner_self_nonneg },
      apply finset.sum_nonneg,
      intros z h,
      exact inner_self_nonneg,
    end,
  nonneg_im :=
    begin
      intro x,
      unfold inner,
      rw[←finset.sum_hom finset.univ complex.im],
      have H : ∀ i, (inner (x i) (x i)).im = 0,
        { intro i, exact inner_self_nonneg_im },
      apply finset.sum_eq_zero,
      intros z h,
      exact inner_self_nonneg_im,
    end,
  definite := λ x h,
    begin
      unfold inner at h,
      have h': ∑ (i : ι), (inner (x i) (x i)).re = 0,
        { rw[finset.sum_hom finset.univ complex.re], simp only [h, zero_re] },
      have H: ∀ i ∈ (finset.univ : finset ι), 0 ≤ (inner (x i) (x i)).re :=
            λ i hi, inner_self_nonneg,
      have H₁ : ∀ i ∈ (finset.univ : finset ι), (inner (x i) (x i)).re = 0,
        { apply (finset.sum_eq_zero_iff_of_nonneg _).mp h', exact H },
      ext,
      apply inner_self_eq_zero.mp,
      ext,
      rw[zero_re],
      apply H₁ _, simp,
      rw[zero_im],
      have H_im: ∀ i ∈ (finset.univ : finset ι), (inner (x i) (x i)).im = 0 :=
            λ i _, inner_self_nonneg_im,
      apply H_im x_1,
      exact finset.mem_univ x_1,
    end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left]
}

/-
The set of complex numbers is a complex inner product space. While the norm given by this
definition is equal to the default norm `∥x∥ = abs x`, it is not definitionally equal, so we
don't turn this definition into an instance.
-/
-- TODO: do the same trick as with `metric_space` and `emetric_space`? -/
def complex.is_complex_inner_product_space : complex_inner_product_space ℂ :=
{ inner := (λ x y, (conj x) * y),
  conj_sym := assume x y,
    by {unfold inner, rw[conj_mul y.conj x, conj_conj, mul_comm]},
  nonneg_re :=
    begin
      intro x,
      unfold inner,
      rw[mul_re, conj_re, conj_im],
      simp only [neg_mul_eq_neg_mul_symm, ge_iff_le, sub_neg_eq_add],
      have H₁ : x.re * x.re ≥ 0,
        exact mul_self_nonneg x.re,
      have H₂ : x.im * x.im ≥ 0,
        exact mul_self_nonneg x.im,
      linarith,
    end,
  nonneg_im :=
    begin
      intro x,
      unfold inner,
      rw[mul_im, conj_re, conj_im],
      ring,
    end,
  definite := assume x,
    begin
      intro H,
      unfold inner at H,
      rw[eq_comm, zero_eq_mul] at H,
      cases H,
      have H₁ : x.conj.conj = (0 : ℂ).conj,
        { exact congr_arg conj H},
      rwa[conj_conj, conj_zero] at H₁,
      exact H,
    end,
  add_left := by { intros x y z, unfold inner, rw[conj_add], ring},
  smul_left :=
    begin
      intros x y z,
      unfold inner,
      simp only [complex.conj_mul, algebra.id.smul_eq_mul],
      ring,
    end
}

/-
Orthogonality: `x` and `y` are orthogonal if `⟨x,y⟩ = 0`.
-/

section orthogonal

variables {ι : Type*}

def is_orthogonal_set (v : ι → α) := ∀ i j : ι, i ≠ j → inner (v i) (v j) = 0

def is_normalized_set (v : ι → α) := ∀ i : ι, inner (v i) (v i) = 1

def is_orthonormal_set (v : ι → α) := is_orthogonal_set v ∧ is_normalized_set v

def is_orthonormal_basis (v : ι → α) := is_basis ℂ v ∧ is_orthonormal_set v

end orthogonal

section instances
/-- The standard complex Euclidean space, functions on a finite type. For an `n`-dimensional space
use `complex_euclidean_space (fin n)`.  -/
@[derive add_comm_group, nolint unused_arguments]
def complex_euclidean_space (n : Type*) [fintype n] : Type* := n → ℂ

variables {ι : Type*} [fintype ι]

instance : inhabited (complex_euclidean_space ι) := ⟨0⟩

local attribute [instance] complex.is_complex_inner_product_space

instance : complex_inner_product_space (complex_euclidean_space ι)
      := pi.complex_inner_product_space (λ _, ℂ)

lemma complex_euclidean_space.inner_def (x y : complex_euclidean_space ι)
      : inner x y = ∑ i, (conj (x i)) * y i := rfl

end instances

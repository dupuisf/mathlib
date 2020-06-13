/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.complex_inner_product

/-!

# Complex Hilbert space

A complex Hilbert space is a complex inner product space that is also a complete metric space
with respect to the distance function induced by the inner product.

## Main results

## Notation

-/

noncomputable theory

universes u v w

variables {α : Type u} {F : Type v} {G : Type w}
variables {ι : Type u} [fintype ι]

class complex_hilbert_space (α : Type u) extends complex_inner_product_space α, complete_space α

/-
Hermitian adjoint
-/

variables {𝓗₁ : Type u} {𝓗₂ : Type u} [complex_hilbert_space 𝓗₁] [complex_hilbert_space 𝓗₂]

def is_adjoint (adj : (𝓗₁ →ₗ[ℂ] 𝓗₂) →ₗ[ℂ] (𝓗₂ →ₗ[ℂ] 𝓗₁)) : Prop := ∀ (A : 𝓗₁ →ₗ[ℂ] 𝓗₂), ∀ x y, inner x (A y) = inner ((adj A) x) y

section instances

instance : uniform_space (complex_euclidean_space ι) := Pi.uniform_space (λ _, ℂ)
instance : complete_space ℂ := complete_of_proper  -- somehow apply_instance takes forever
instance : complete_space (complex_euclidean_space ι) := Pi.complete (λ _, ℂ)

end instances

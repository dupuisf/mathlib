/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.normed_space.complex_inner_product
import set_theory.cardinal

/-!

# Complex Hilbert space

A complex Hilbert space is a complex inner product space that is also a complete metric space
with respect to the distance function induced by the inner product.

## Main results

## Notation

-/

noncomputable theory

universes u v w

variables {ι : Type*} [fintype ι]

/-
Not good: I need to make sure it is complete *with respect to the distance induced by the
inner product*, and not whatever distance this Pi.uniform_space thing gives me.
-/

section prio

set_option default_priority 100 -- see Note [default priority]
class complex_hilbert_space (V : Type u) [complex_inner_product_space V] :=
  (is_complete := complete_space V)

class separable (V : Type u) [add_comm_group V] [vector_space ℂ V] [complex_inner_product_space V] [complex_hilbert_space V] :=
  (countable_dim := vector_space.dim ℂ V ≤ cardinal.omega)

end prio



/-
Show that the standard complex Euclidean space is a complex Hilbert space
-/
section instances

--instance : uniform_space (complex_euclidean_space ι) := Pi.uniform_space (λ _, ℂ)
#print instances uniform_space
instance : complete_space ℂ := complete_of_proper  -- somehow apply_instance takes forever
instance : complete_space (complex_euclidean_space ι) := Pi.complete (λ _, ℂ)
#check complex_hilbert_space ι
--def foo : complex_hilbert_space (complex_euclidean_space ι) := by apply_instance


end instances

/-
Hermitian adjoint
-/

variables {𝓗₁ : Type u} {𝓗₂ : Type u} [complex_hilbert_space 𝓗₁] [complex_hilbert_space 𝓗₂]

def is_adjoint (adj : (𝓗₁ →ₗ[ℂ] 𝓗₂) →ₗ[ℂ] (𝓗₂ →ₗ[ℂ] 𝓗₁)) : Prop := ∀ (A : 𝓗₁ →ₗ[ℂ] 𝓗₂), ∀ x y, inner x (A y) = inner ((adj A) x) y

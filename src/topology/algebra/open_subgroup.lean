/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.filter.lift
import topology.opens
import topology.algebra.ring

section
open topological_space
variables (G : Type*) [group G] [topological_space G]

/-- The type of open subgroups of a topological group. -/
@[to_additive open_add_subgroup]
def open_subgroup := { U : subgroup G // is_open (U : set G) }

@[to_additive]
instance open_subgroup.has_coe_to_opens :
  has_coe (open_subgroup G) (opens G) := ⟨λ U, ⟨U.1, U.2⟩⟩

@[to_additive]
instance open_subgroup.has_coe_to_subgroup :
  has_coe (open_subgroup G) (subgroup G) := ⟨λ U, U.1⟩
end

-- Tell Lean that `open_add_subgroup` is a namespace
namespace open_add_subgroup
end open_add_subgroup

namespace open_subgroup
open function topological_space
open_locale topological_space
variables {G : Type*} [group G] [topological_space G]
variables {U V : open_subgroup G}

@[to_additive]
instance : has_mem G (open_subgroup G) := ⟨λ g U, g ∈ (U : set G)⟩

@[to_additive]
lemma ext : (U = V) ↔ ((U : set G) = V) :=
⟨ λ h, by rw h,
  λ h, by {cases U with U _, cases V with V _, congr, cases U, cases V, congr, exact h } ⟩

@[ext, to_additive]
lemma ext' (h : (U : set G) = V) : (U = V) :=
ext.mpr h

@[to_additive]
lemma coe_injective : injective (λ U : open_subgroup G, (U : set G)) :=
λ U V h, ext' h

variable (U)
@[to_additive]
protected lemma is_open : is_open (U : set G) := U.2

@[to_additive]
protected lemma one_mem : (1 : G) ∈ U :=
U.1.one_mem

@[to_additive]
protected lemma inv_mem {g : G} (h : g ∈ U) : g⁻¹ ∈ U :=
U.1.inv_mem h

@[to_additive]
protected lemma mul_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ * g₂ ∈ U :=
U.1.mul_mem h₁ h₂

@[to_additive]
lemma mem_nhds_one : (U : set G) ∈ 𝓝 (1 : G) :=
mem_nhds_sets U.is_open U.one_mem
variable {U}

@[to_additive]
instance : inhabited (open_subgroup G) :=
{ default := ⟨⊤, is_open_univ⟩ }

@[to_additive]
lemma is_open_of_nonempty_open_subset [topological_monoid G] {s : set G} [is_subgroup s]
  (h : ∃ U : opens G, nonempty U ∧ (U : set G) ⊆ s) :
  is_open s :=
begin
  rw is_open_iff_forall_mem_open,
  intros x hx,
  rcases h with ⟨U, ⟨g, hg⟩, hU⟩,
  use (λ y, y * (x⁻¹ * g)) ⁻¹' U,
  split,
  { intros u hu,
    erw set.mem_preimage at hu,
    replace hu := hU hu,
    replace hg := hU hg,
    have : (x⁻¹ * g)⁻¹ ∈ s,
    { simp [*, is_subgroup.inv_mem, is_submonoid.mul_mem], },
    convert is_submonoid.mul_mem hu this, simp [mul_assoc] },
  split,
  { exact continuous_id.mul continuous_const _ U.property },
  { change  x * (x⁻¹ * g) ∈ U,
    convert hg,
    rw [← mul_assoc, mul_right_inv, one_mul] }
end

@[to_additive is_open_of_open_add_subgroup]
lemma is_open_of_open_subgroup [topological_monoid G] {s : subgroup G}
  (h : ∃ U : open_subgroup G, (U : set G) ⊆ s) : is_open (s : set G) :=
is_open_of_nonempty_open_subset $ let ⟨U, hU⟩ := h in ⟨U, ⟨⟨1, U.one_mem⟩⟩, hU⟩

@[to_additive]
lemma is_closed [topological_monoid G] (U : open_subgroup G) : is_closed (U : set G) :=
begin
  show is_open (-(U : set G)),
  rw is_open_iff_forall_mem_open,
  intros x hx,
  use (λ y, y * x⁻¹) ⁻¹' U,
  split,
  { intros u hux,
    erw set.mem_preimage at hux,
    rw set.mem_compl_iff at hx ⊢,
    intro hu, apply hx,
    simpa using U.mul_mem (U.inv_mem hux) hu },
  split,
  { exact (continuous_mul_right _) _ U.is_open },
  { simpa using U.one_mem }
end

section
variables {H : Type*} [group H] [topological_space H]

@[to_additive]
def prod (U : open_subgroup G) (V : open_subgroup H) : open_subgroup (G × H) :=
⟨(U : subgroup G).prod (V : subgroup H), is_open_prod U.is_open V.is_open⟩

end

@[to_additive]
instance : partial_order (open_subgroup G) := partial_order.lift _ coe_injective (by apply_instance)

@[to_additive]
instance : semilattice_inf_top (open_subgroup G) :=
{ inf := λ U V, ⟨U ⊓ V, is_open_inter U.is_open V.is_open⟩,
  inf_le_left := λ U V, set.inter_subset_left _ _,
  inf_le_right := λ U V, set.inter_subset_right _ _,
  le_inf := λ U V W hV hW, set.subset_inter hV hW,
  top := default _,
  le_top := λ U, set.subset_univ _,
  ..open_subgroup.partial_order }

#check subgroup.closure_union

@[to_additive]
instance [topological_monoid G] : semilattice_sup_top (open_subgroup G) :=
{ sup := λ U V,
  { val := U ⊔ V,
    property :=
    begin
      { refine is_open_of_open_subgroup _,
        exact ⟨U, set.subset.trans (set.subset_union_left U V) (subgroup.union_subset_sup _ _)⟩ },
    end },
  le_sup_left := λ U V, @le_sup_left (subgroup G) _ U V,
  le_sup_right := λ U V, @le_sup_right (subgroup G) _ U V,
  sup_le := λ U V W, @sup_le (subgroup G) _ U V W,
  ..open_subgroup.semilattice_inf_top }

@[simp, to_additive] lemma coe_inf : (↑(U ⊓ V) : set G) = (U : set G) ∩ V := rfl

@[to_additive] lemma le_iff : U ≤ V ↔ (U : set G) ⊆ V := iff.rfl

end open_subgroup

namespace submodule
open open_add_subgroup
variables {R : Type*} {M : Type*} [comm_ring R]
variables [add_comm_group M] [topological_space M] [topological_add_group M] [module R M]

lemma is_open_of_open_submodule {P : submodule R M}
  (h : ∃ U : submodule R M, is_open (U : set M) ∧ U ≤ P) : is_open (P : set M) :=
let ⟨U, h₁, h₂⟩ := h in
is_open_of_open_add_subgroup ⟨⟨U.to_add_subgroup, h₁⟩, λ x hx, h₂ _⟩

end submodule

namespace ideal
variables {R : Type*} [comm_ring R]
variables [topological_space R] [topological_ring R]

lemma is_open_of_open_subideal {I : ideal R}
  (h : ∃ U : ideal R, is_open (U : set R) ∧ U ≤ I) : is_open (I : set R) :=
submodule.is_open_of_open_submodule h

end ideal

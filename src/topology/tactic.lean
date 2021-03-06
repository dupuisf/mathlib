/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import topology.basic
/-!
# Tactics for topology

Currently we have one domain-specific tactic for topology: `continuity`.

-/

/-!
### `continuity` tactic

Automatically solve goals of the form `continuous f`.

Mark lemmas with `@[continuity]` to add them to the set of lemmas
used by `continuity`. Note: `to_additive` doesn't know yet how to
copy the attribute to the additive version.
-/

/-- User attribute used to mark tactics used by `continuity`. -/
@[user_attribute]
meta def continuity : user_attribute :=
{ name := `continuity,
  descr := "lemmas usable to prove continuity" }

-- Mark some continuity lemmas already defined in `topology.basic`
attribute [continuity]
  continuous_id
  continuous_const

namespace tactic

/--
Tactic to apply `continuous.comp` when appropriate.

Applying `continuous.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `continuous f`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `continuous (λ x, f x)` and
  produce new goals `continuous (λ x, x)`, `continuous f`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
meta def apply_continuous.comp : tactic unit :=
`[fail_if_success { exact continuous_const };
  refine continuous.comp _ _;
  fail_if_success { exact continuous_id }]

/-- List of tactics used by `continuity` internally. -/
meta def continuity_tactics : list (tactic string) :=
[
  `[apply_rules continuity]            >> pure "apply_rules continuity",
  -- auto_cases,
  intros1                              >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  tactic.interactive.apply_assumption  >> pure "apply_assumption",
  apply_continuous.comp                >> pure "refine continuous.comp _ _"
]

namespace interactive

/-- Solve goals of the form `continuous f`. -/
meta def continuity (cfg : tidy.cfg := {}) : tactic unit :=
with_local_reducibility `continuous decl_reducibility.irreducible $
tactic.tidy { tactics := continuity_tactics, ..cfg }

/-- Version of `continuity` for use with auto_param. -/
meta def continuity' : tactic unit := continuity

/--
`continuity` solves goals of the form `continuous f` by applying lemmas tagged with the
`continuity` user attribute.

```
example {X Y : Type*} [topological_space X] [topological_space Y]
  (f₁ f₂ : X → Y) (hf₁ : continuous f₁) (hf₂ : continuous f₂)
  (g : Y → ℝ) (hg : continuous g) : continuous (λ x, (max (g (f₁ x)) (g (f₂ x))) + 1) :=
by continuity
```
will discharge the goal, generating a proof term like
`((continuous.comp hg hf₁).max (continuous.comp hg hf₂)).add continuous_const`
-/
add_tactic_doc
{ name := "continuity / continuity'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.continuity, `tactic.interactive.continuity'],
  tags := ["lemma application"]
}

end interactive

end tactic

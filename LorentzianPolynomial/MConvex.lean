/-
Copyright (c) 2026 Jaehyeon Seo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaehyeon Seo
-/
module

public import Mathlib.Data.Finsupp.Order

/-!
# M-convex sets

This file defines M-convex subsets of finitely supported natural-number vectors using the
symmetric exchange axiom.

## Main declaration

* `Set.MConvex`: A predicate asserting that a set of finitely supported natural-number vectors is
  M-convex.
-/

@[expose] public section

namespace Set

variable {σ : Type*}

/-- A set of finitely supported natural-number vectors is M-convex if it satisfies the symmetric
exchange axiom: whenever `x i > y i`, one can exchange one unit from `i` to some coordinate `j`
with `x j < y j`, while remaining in the set in both directions. -/
def MConvex (s : Set (σ →₀ ℕ)) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ i, y i < x i →
    ∃ j, x j < y j ∧
      x - Finsupp.single i 1 + Finsupp.single j 1 ∈ s ∧
      y - Finsupp.single j 1 + Finsupp.single i 1 ∈ s

end Set

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-
Copyright (c) 2026 Miraj Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miraj Samarakkody
-/

/-!
# Characterization of linear maps with equal kernels

Let `V` is finite dimensional and `S, T ∈ L (V,W)`. Then `null S = null T` if and only if
if there exists an invertible `E ∈ L(V)` such that `S = ET`.

## Main results
-/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V ]

theorem null_eq_iff_exists_invertibles (S T : V →ₗ[K] W) :
  LinearMap.ker S = LinearMap.ker T ↔
  ∃ E : W ≃ₗ[K] W, S = E ∘ₗ T := by
sorry

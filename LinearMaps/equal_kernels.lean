import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Projection


/-
Copyright (c) 2026 Miraj Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miraj Samarakkody
-/

/-!
# Characterization of linear maps with equal kernels

This file proves that two linear maps `S, T : V →ₗ[K] W` have equal kernels
if and only if there exists an automorphism `E : W ≃ₗ[K] W` such that `S = E ∘ T`.

## Main results

* `LinearMap.ker_eq_ker_iff_exists_linearEquiv_comp`: The main characterization theorem.
* `LinearMap.ker_comp_linearEquiv`: If `S = E ∘ T` for `E : W ≃ₗ[K] W`, then `ker S = ker T`.

## References

* Sheldon Axler, *Linear Algebra Done Right*, Chapter 3

## Tags

linear map, kernel, automorphism, linear equivalence
-/

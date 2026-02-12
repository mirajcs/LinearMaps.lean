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

Let `V` is finite dimesional and `S, T ∈ L (V,W)`. Then `null S = null T` if and only if
if there exists an invertible `E ∈ L(V)` such that `S = TE`.

## Main results

* `LinearMap.ker_eq_ker_iff_exists_linearEquiv_comp`: The main characterization theorem.
* `LinearMap.ker_comp_linearEquiv`: If `S = E ∘ T` for `E ∈ L(V)`, then `ker S = ker T`.

-/

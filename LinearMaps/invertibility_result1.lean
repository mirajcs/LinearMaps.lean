import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-
Copyright (c) 2026 Miraj Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miraj Samarakkody
-/

/-!
# Invertibility of a linear map from a three-factor identity

Let `V` be finite dimensional and `S, T, U ∈ L(V)`. If `STU = I`,
then `T` is invertible with `T⁻¹ = US`.

## Main results

- `stu_eq_id_invertible` : If `S * T * U = 1` in `Module.End K V`, then `US` is a
  two-sided inverse of `T`, i.e. `T * (U * S) = 1` and `(U * S) * T = 1`.
-/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If `S * T * U = 1`, then `S * T` is invertible.
Proof: `S * T` is surjective (since `(S*T)(U v) = v`), and surjective endomorphisms of
finite-dimensional spaces are bijective, hence invertible. -/
lemma st_isUnit (S T U : Module.End K V) (h : S * T * U = 1) : IsUnit (S * T) := by
  rw [Module.End.isUnit_iff]
  have hSurj : Function.Surjective (S * T) := fun v =>
    ⟨U v, by have := LinearMap.congr_fun h v; simp only [Module.End.mul_apply,
        Module.End.one_apply] at this; exact this⟩
  exact ⟨LinearMap.injective_iff_surjective.mpr hSurj, hSurj⟩


/-- In a finite-dimensional space, `S * T` is invertible if and only if both `S` and `T`
are individually invertible. -/
theorem isUnit_mul_iff (S T : Module.End K V) :
    IsUnit (S * T) ↔ IsUnit S ∧ IsUnit T := by
  simp only [Module.End.isUnit_iff]
  constructor
  · intro ⟨h_inj, h_surj⟩
    constructor
    · -- S is surjective (from ST surjective), hence bijective by fin-dim
      have hS_surj : Function.Surjective S := fun v => by
        obtain ⟨u, hu⟩ := h_surj v
        simp only [Module.End.mul_apply] at hu
        exact ⟨T u, hu⟩
      exact ⟨LinearMap.injective_iff_surjective.mpr hS_surj, hS_surj⟩
    · -- T is injective (from ST injective), hence bijective by fin-dim
      have hT_inj : Function.Injective T := fun x y hxy => by
        apply h_inj; simp only [Module.End.mul_apply, hxy]
      exact ⟨hT_inj, LinearMap.injective_iff_surjective.mp hT_inj⟩
  · intro ⟨⟨hS_inj, hS_surj⟩, ⟨hT_inj, hT_surj⟩⟩
    constructor
    · -- (S * T) injective: T injects then S injects
      intro x y hxy
      simp only [Module.End.mul_apply] at hxy
      exact hT_inj (hS_inj hxy)
    · -- (S * T) surjective: T surjects then S surjects
      intro v
      obtain ⟨w, hw⟩ := hS_surj v
      obtain ⟨u, hu⟩ := hT_surj w
      exact ⟨u, by simp only [Module.End.mul_apply, hu, hw]⟩

/-- From `STU = I`, `T` itself is invertible.
Proof: `ST` is invertible (`st_isUnit`), and 
`isUnit_mul_iff` extracts invertibility of each factor. -/
lemma t_isUnit (S T U : Module.End K V) (h : S * T * U = 1) : IsUnit T :=
  ((isUnit_mul_iff S T).mp (st_isUnit S T U h)).2

/-- If `S`, `T`, `U` are linear endomorphisms of a finite-dimensional space with `STU = I`,
then `T` is invertible and `T⁻¹ = US`. We express this as: `US` is a two-sided inverse of `T`. -/
theorem stu_eq_id_invertible (S T U : Module.End K V) (h : S * T * U = 1) :
    T * (U * S) = 1 ∧ (U * S) * T = 1 := by
  have hST := st_isUnit S T U h
  have hS  := ((isUnit_mul_iff S T).mp hST).1
  -- S * (T * U) = 1  (same as h, just reassociated)
  have h_STU : S * (T * U) = 1 := by rw [← mul_assoc]; exact h
  -- U * (S * T) = 1 : cancel (S * T) from  (S*T) * (U*(S*T)) = (S*T) * 1
  have h_UST : U * (S * T) = 1 :=
    hST.mul_left_cancel (by rw [← mul_assoc, h, one_mul, mul_one])
  -- (T * U) * S = 1 : cancel S from  S * ((T*U)*S) = S * 1
  have h_TUS : (T * U) * S = 1 :=
    hS.mul_left_cancel (by rw [← mul_assoc, h_STU, one_mul, mul_one])
  exact ⟨by rw [← mul_assoc]; exact h_TUS,
         by rw [mul_assoc];  exact h_UST⟩


/-- The previous result fails for infinite-dimensional spaces.
    Counterexample: V = ℕ → K (all K-valued sequences),
    S = left shift  (S f)(n) = f(n+1),
    T = identity,
    U = right shift (U f)(0) = 0, (U f)(n+1) = f(n).
    Then S * T * U = 1, but T * (U * S) = R * L ≠ 1:
    (R * L)(fun _ => 1) evaluates to 0 at position 0, not 1. -/
example : ∃ (S T U : Module.End K (ℕ → K)), S * T * U = 
  1 ∧ ¬(T * (U * S) = 1 ∧ (U * S) * T = 1) := by
  -- S = left shift
  let L : Module.End K (ℕ → K) :=
    { toFun    := fun f n => f (n + 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- U = right shift
  let R : Module.End K (ℕ → K) :=
    { toFun    := fun f n => Nat.casesOn n 0 f
      map_add' := fun f g => by funext n; cases n <;> simp
      map_smul' := fun c f => by funext n; cases n <;> simp }
  refine ⟨L, 1, R, ?_, ?_⟩
  · -- L * 1 * R = 1 : left shift ∘ right shift = identity
    ext f n
    simp only [Module.End.mul_apply, Module.End.one_apply]
    rfl
  · -- 1 * (R * L) ≠ 1 because (R * L)(fun _ => 1) 0 = 0 ≠ 1
    rintro ⟨h, -⟩
    rw [one_mul] at h  -- h : R * L = 1
    have key  : (R * L : Module.End K (ℕ → K)) (fun _ => (1 : K)) 0 = 0 := rfl
    have key2 : (1   : Module.End K (ℕ → K)) (fun _ => (1 : K)) 0 = 1 := rfl
    rw [h] at key
    exact one_ne_zero (key2.symm.trans key)

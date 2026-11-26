/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Array
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Array-backed matrices of linear maps

Store the entries of a matrix in an array so repeated lookups can reuse them.
-/

public section

variable {R : Type*} [CommSemiring R] {m n : ℕ}

/-- Compute and store the matrix entries of a linear map in an array, with a certificate that
multiplication by the resulting matrix gives the original map. -/
def LinearMap.materializeMatrix (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    {A : Matrix (Fin m) (Fin n) R // A.mulVecLin = f} := by
  let A := LinearMap.toMatrix' f
  let entries := A.toArray
  exact ⟨Matrix.ofArray entries A.size_toArray, by
    simpa only [entries, A, Matrix.ofArray_toArray, Matrix.toLin'_apply']
      using Matrix.toLin'_toMatrix' f⟩

/-- Each entry of the stored matrix is a coordinate of the image of a standard unit vector. -/
@[simp]
theorem LinearMap.materializeMatrix_apply (f : (Fin n → R) →ₗ[R] (Fin m → R))
    (i : Fin m) (j : Fin n) :
    f.materializeMatrix.val i j = f (Pi.single j 1) i := by
  have h := LinearMap.congr_fun f.materializeMatrix.property (Pi.single j 1)
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply]
    using congrFun h i

/-- Implement the forward map of a linear equivalence using an array of its matrix entries.
The inverse is inherited from the original equivalence. -/
def LinearEquiv.withCachedMatrix (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) :
    (Fin n → R) ≃ₗ[R] (Fin m → R) := by
  let A := e.toLinearMap.materializeMatrix
  exact
    { A.val.mulVecLin with
      invFun := e.symm
      left_inv := fun x ↦ by rw [A.property]; exact e.symm_apply_apply x
      right_inv := fun x ↦ by rw [A.property]; exact e.apply_symm_apply x }

/-- The array-backed equivalence has the same forward action as the original. -/
@[simp]
theorem LinearEquiv.withCachedMatrix_apply (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) (x : Fin n → R) :
    e.withCachedMatrix x = e x := by
  simp only [LinearEquiv.withCachedMatrix, LinearEquiv.coe_mk]
  exact LinearMap.congr_fun e.toLinearMap.materializeMatrix.property x

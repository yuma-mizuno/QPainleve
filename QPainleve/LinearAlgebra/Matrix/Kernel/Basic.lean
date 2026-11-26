/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import QPainleve.LinearAlgebra.Matrix.Array

/-!
# Computing bases of integral matrix kernels

A Bézout change of coordinates reduces a row to one coefficient. If that
coefficient is nonzero, the equation sets its coordinate to zero. Applying
this procedure to the remaining equations in the resulting coordinates gives
an integral basis of the whole kernel. The computation also handles zero rows
and matrices with no rows or no columns.
-/

public section

open Module

namespace Matrix

private def bezoutEquiv (a b : ℤ) :
    {e : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) //
      ∀ x, a * (e x).1 + b * (e x).2 = (a.gcd b : ℤ) * x.1} := by
  by_cases h : a.gcd b = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h
    exact ⟨LinearEquiv.refl ℤ _, by simp⟩
  let g : ℤ := a.gcd b
  let p := a / g
  let q := b / g
  let s := a.gcdA b
  let t := a.gcdB b
  have ha : p * g = a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hb : q * g = b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hg : g ≠ 0 := Int.ofNat_ne_zero.mpr h
  have hgcd : g = a * s + b * t := Int.gcd_eq_gcd_ab a b
  have hs : p * s + q * t = 1 := by
    apply mul_right_cancel₀ hg
    calc
      (p * s + q * t) * g = (p * g) * s + (q * g) * t := by ring
      _ = 1 * g := by rw [ha, hb, one_mul, hgcd]
  let e : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) := by
    refine
      { toFun := fun x ↦ (s * x.1 - q * x.2, t * x.1 + p * x.2)
        invFun := fun x ↦ (p * x.1 + q * x.2, -t * x.1 + s * x.2)
        left_inv := fun x ↦ Prod.ext ?_ ?_
        right_inv := fun x ↦ Prod.ext ?_ ?_
        map_add' := fun x y ↦ Prod.ext (by dsimp; ring) (by dsimp; ring)
        map_smul' := fun c x ↦ Prod.ext (by dsimp; ring) (by dsimp; ring) } <;>
      dsimp
    · linear_combination x.1 * hs
    · linear_combination x.2 * hs
    · linear_combination x.1 * hs
    · linear_combination x.2 * hs
  have hcross : a * q = b * p := by
    apply mul_right_cancel₀ hg
    rw [mul_assoc, mul_assoc, ha, hb, mul_comm]
  refine ⟨e, fun x ↦ ?_⟩
  calc
    _ = a * (s * x.1 - q * x.2) + b * (t * x.1 + p * x.2) := rfl
    _ = _ := by linear_combination -x.1 * hgcd - x.2 * hcross

private def headPairEquiv (n : ℕ) :
    ((ℤ × ℤ) × (Fin n → ℤ)) ≃ₗ[ℤ] (Fin (n + 2) → ℤ) :=
  let tail := Fin.consLinearEquiv ℤ (fun _ : Fin (n + 1) ↦ ℤ)
  let head := Fin.consLinearEquiv ℤ (fun _ : Fin (n + 2) ↦ ℤ)
  (LinearEquiv.prodAssoc ℤ ℤ ℤ (Fin n → ℤ)).trans
    (((LinearEquiv.refl ℤ ℤ).prodCongr tail).trans head)

private def reduceRow : ∀ {n : ℕ} (a : Fin (n + 1) → ℤ),
    {p : ℤ × ((Fin (n + 1) → ℤ) ≃ₗ[ℤ] (Fin (n + 1) → ℤ)) //
      ∀ x, a ⬝ᵥ p.2 x = p.1 * x 0}
  | 0, a => ⟨(a 0, LinearEquiv.refl ℤ _), by simp [dotProduct]⟩
  | n + 1, a => by
    let tail := reduceRow (vecTail a)
    let step := bezoutEquiv (a 0) tail.val.1
    let splitPair := headPairEquiv n
    let mix := splitPair.symm.trans
      ((step.val.prodCongr (LinearEquiv.refl ℤ _)).trans splitPair)
    let splitHead := Fin.consLinearEquiv ℤ (fun _ : Fin (n + 2) ↦ ℤ)
    let liftTail := splitHead.symm.trans
      (((LinearEquiv.refl ℤ ℤ).prodCongr tail.val.2).trans splitHead)
    let e := mix.trans liftTail
    refine ⟨(Int.gcd (a 0) tail.val.1, e.withCachedMatrix), fun x ↦ ?_⟩
    rw [LinearEquiv.withCachedMatrix_apply]
    let z := step.val (x 0, x 1)
    have ht : a ⬝ᵥ e x = a 0 * z.1 + vecTail a ⬝ᵥ tail.val.2 (vecCons z.2 (vecTail (vecTail x))) :=
      dotProduct_cons ..
    rw [ht, tail.property]
    exact step.property (x 0, x 1)

private def zeroHeadEquiv (n : ℕ) :
    (Fin n → ℤ) ≃ₗ[ℤ] (LinearMap.proj (R := ℤ) (φ := fun _ : Fin (n + 1) ↦ ℤ) 0).ker where
  toFun x := ⟨vecCons 0 x, rfl⟩
  invFun x := vecTail x.val
  left_inv _ := rfl
  right_inv x := Subtype.ext <| funext <| Fin.cases
    (LinearMap.mem_ker.mp x.property).symm (fun _ ↦ rfl)
  map_add' _ _ := Subtype.ext <| funext <| Fin.cases rfl (fun _ ↦ rfl)
  map_smul' _ _ := Subtype.ext <| funext <| Fin.cases (by simp) (fun _ ↦ rfl)

private def rowKernelEquiv {n : ℕ} (a : Fin n → ℤ) :
    Σ k : ℕ, (Fin k → ℤ) ≃ₗ[ℤ] (dotProductBilin ℤ ℤ a).ker := by
  by_cases ha : a = 0
  · subst a
    exact ⟨n, (LinearEquiv.ofTop _ (by simp)).symm⟩
  cases n with
  | zero => exact (ha (Subsingleton.elim _ _)).elim
  | succ n =>
    let row := reduceRow a
    let f := dotProductBilin ℤ ℤ a
    let e := row.val.2
    have hnonzero : row.val.1 ≠ 0 := by
      intro hz
      apply ha
      ext i
      obtain ⟨x, hx⟩ := e.surjective (Pi.single i 1)
      have hxi : row.val.2 x = Pi.single i 1 := hx
      simpa only [hxi, dotProduct_single_one, hz, zero_mul, Pi.zero_apply] using row.property x
    have hker : f.ker.comap e.toLinearMap =
        (LinearMap.proj (R := ℤ) (φ := fun _ : Fin (n + 1) ↦ ℤ) 0).ker := by
      ext x
      simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap,
        LinearMap.proj_apply]
      have hx : f (e x) = row.val.1 * x 0 := row.property x
      rw [hx]
      exact ⟨fun hzero ↦ (mul_eq_zero.mp hzero).resolve_left hnonzero, fun he ↦ by simp [he]⟩
    exact ⟨n, (zeroHeadEquiv n).trans <| (LinearEquiv.ofEq _ _ hker.symm).trans <|
      e.ofSubmodule' f.ker⟩

private def tailRows {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) ℤ) :
    (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
  (A.submatrix Fin.succ id).mulVecLin

private theorem ker_comap_tailRows {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) ℤ) :
    A.mulVecLin.ker.comap (dotProductBilin ℤ ℤ (A 0)).ker.subtype =
      ((tailRows A).comp (dotProductBilin ℤ ℤ (A 0)).ker.subtype).ker := by
  ext x
  simp only [Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.comp_apply]
  constructor
  · intro h
    funext i
    exact congrFun h i.succ
  · intro h
    refine funext (Fin.cases ?_ fun i ↦ congrFun h i)
    exact LinearMap.mem_ker.mp x.property

private def intKernelEquiv : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ),
    Σ k : ℕ, (Fin k → ℤ) ≃ₗ[ℤ] A.mulVecLin.ker
  | 0, _, A =>
    ⟨_, (LinearEquiv.ofTop _ (LinearMap.ker_eq_top.mpr <| LinearMap.ext fun _ ↦
      funext fun i ↦ i.elim0)).symm⟩
  | m + 1, _, A => by
    let row := rowKernelEquiv (A 0)
    let K := (dotProductBilin ℤ ℤ (A 0)).ker
    let endRows := (tailRows A).comp K.subtype
    let f := endRows.comp row.2.toLinearMap
    let B := f.materializeMatrix
    let rest := intKernelEquiv B.val
    have hker : B.val.mulVecLin.ker = endRows.ker.comap row.2.toLinearMap :=
      (congrArg LinearMap.ker B.property).trans (LinearMap.ker_comp _ _)
    have hle : A.mulVecLin.ker ≤ K :=
      fun _ hx ↦ congrFun (LinearMap.mem_ker.mp hx) 0
    exact ⟨rest.1, rest.2.trans <| (LinearEquiv.ofEq _ _ hker).trans <|
      (row.2.ofSubmodule' endRows.ker).trans <|
      (LinearEquiv.ofEq _ _ (ker_comap_tailRows A).symm).trans <|
      Submodule.comapSubtypeEquivOfLe hle⟩

/-- The number and ambient coordinates of the computed integral kernel basis vectors. -/
def intKernelBasisVectors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Σ k : ℕ, Fin k → Fin n → ℤ :=
  let e := intKernelEquiv A
  ⟨e.1, fun j ↦ (e.2 (Pi.single j 1)).val⟩

/-- The computable coordinate equivalence for the integral basis of the matrix kernel. -/
def intKernelBasisEquiv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    A.mulVecLin.ker ≃ₗ[ℤ] (Fin A.intKernelBasisVectors.1 → ℤ) :=
  (intKernelEquiv A).2.symm

/-- The integral basis of the matrix kernel whose ambient vectors are computed by
`intKernelBasisVectors`. -/
noncomputable def intKernelBasis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Basis (Fin A.intKernelBasisVectors.1) ℤ A.mulVecLin.ker :=
  Basis.ofEquivFun A.intKernelBasisEquiv

/-- The computed coordinate equivalence agrees with the basis coordinate equivalence. -/
@[simp]
theorem intKernelBasis_equivFun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    A.intKernelBasis.equivFun = A.intKernelBasisEquiv :=
  Basis.equivFun_ofEquivFun _

/-- The inverse coordinate equivalence sends a standard unit vector to the corresponding
integral kernel basis vector. -/
@[simp]
theorem intKernelBasisEquiv_symm_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (j : Fin A.intKernelBasisVectors.1) :
    A.intKernelBasisEquiv.symm (Pi.single j 1) = A.intKernelBasis j := by
  rw [← intKernelBasis_equivFun, Basis.equivFun_symm_single]

/-- The ambient coordinates of the integral kernel basis are the computed vectors. -/
@[simp]
theorem intKernelBasis_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (j : Fin A.intKernelBasisVectors.1) :
    (A.intKernelBasis j : Fin n → ℤ) = A.intKernelBasisVectors.2 j := by
  rw [← intKernelBasisEquiv_symm_single]
  rfl

end Matrix

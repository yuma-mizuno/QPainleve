/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Reorder

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class

/-!
# Strict transforms after inserting a point blowup

Inserting a point blowup before a resolving tower preserves the strict-transform
coefficients at the original stages, provided the reordering identifies the
total exceptional classes. The comparison uses the strict transform on the first
blowup as the starting curve for the new tail.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

/-- Appending blowups leaves the strict-transform coefficient at every
earlier stage unchanged. -/
theorem strictTransformCoefficients_append_castAdd {X Y Z : Scheme.{u}} {m n : ℕ}
    {T : BlowupTower X m Y} {U : BlowupTower Y n Z}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (C : X.IdealSheafData)
    (j : Fin m) :
    (hT.append hU).strictTransformCoefficients C (j.castAdd n) =
      hT.strictTransformCoefficients C j := by
  induction hU with
  | nil => simp
  | snoc hU p hp hI ih =>
    simpa only [← Fin.castSucc_castAdd, append_snoc, strictTransformCoefficients_snoc_castSucc]
      using ih

variable {X Y Z : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  {C : X.IdealSheafData} [IrreducibleSpace C.subscheme]
  [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

local notation "I[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

include f in
/-- Suppose a blowup appended over a closed point of the base is moved to the
front, and its ordered tail identifies the original total exceptional classes.
The coefficients of a regular Cartier curve at all original stages are unchanged,
including when the inserted point itself belongs to the curve. -/
theorem strictTransformCoefficients_tail_prepend
    (hT : IsClosedPointTower X T) {p : X} (hp : IsClosed ({p} : Set X))
    {I : X.IdealSheafData} (hI : I = I[p])
    {q : Y} (hq : IsClosed ({q} : Set Y)) (hA : I.comap T.toBase = I[q])
    {U : BlowupTower I.blowup n Z} (hU : IsClosedPointTower I.blowup U)
    (e : (I.comap T.toBase).blowup ≅ Z)
    (he : e.hom ≫ U.toBase ≫ I.blowupToBase = (I.comap T.toBase).blowupToBase ≫ T.toBase)
    (hpic : ∀ x : Fin n → ℤ,
      pullback (e.inv ≫ (I.comap T.toBase).blowupToBase) (T.picardHom (0, x)).toMul =
        (((BlowupTower.nil.snoc I).append U).picardHom
          (0, Fin.addCases (fun _ : Fin 1 ↦ 0) x)).toMul)
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1) :
    hU.strictTransformCoefficients (I.blowupMap C.subschemeι).ker =
      hT.strictTransformCoefficients C := by
  subst I
  let A := (I[p]).comap T.toBase
  have hhead : pullback e.hom (pullback U.toBase (I[p]).blowupExceptionalClass) =
      (T.snoc A).exceptionalClass (Fin.last n) := by
    have hmap := (I[p]).eq_blowupMap T.toBase (h := e.hom ≫ U.toBase)
      ((Category.assoc _ _ _).trans he)
    rw [pullback_comp, hmap, pullback_blowupExceptionalClass_blowupMap,
      exceptionalClass_snoc_last, blowupExceptionalClass_def]
  have htail (j : Fin n) : pullback e.hom (U.exceptionalClass j) =
      (T.snoc A).exceptionalClass ((Fin.last n).succAbove j) := by
    have hzero : (BlowupTower.nil.snoc (I[p])).picardHom (0, fun _ ↦ 0) = 0 := map_zero _
    have h := hpic (Pi.single j 1)
    simp only [picardHom_append, Fin.addCases_left, Fin.addCases_right, hzero,
      picardHom_apply_single, zpow_one] at h
    rw [← h, pullback_comp, Iso.hom_inv_id_assoc,
      Fin.succAbove_last_apply, exceptionalClass_snoc_castSucc]
  have h := (hT.snoc q hq hA).strictTransformCoefficients_tail_move_to_front f
    (.snoc .nil p hp rfl) hU e (Fin.last n) (he.trans (toBase_snoc T A).symm)
    hhead htail hC hdim
  funext j
  simpa only [Function.comp_apply, Fin.succAbove_last_apply,
    strictTransformCoefficients_snoc_castSucc]
    using congrFun h j

end QPainleve.BlowupTower.IsClosedPointTower

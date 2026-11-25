/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Subdivision
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Picard.Hirzebruch

import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Prepend
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Transport
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import QPainleve.Geometry.Toric.Fan.Ruling.FixedPoint
import QPainleve.Geometry.Toric.Fan.Subdivision.StrictTransform

/-!
# Toric preparation of a Hirzebruch resolution

A toric elementary transformation can be used to change the Hirzebruch parameter
even when its center is absent from a specified resolution. Insert that blowup
with coefficient zero, and transport the ordered tail through the common toric
model. The resulting resolution has the same ruling fiber degree. Its new
reverse center has order equal to that degree.

This is the absent-corner step in Case C of Proposition 8.11 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.Toric
open LineBundleClass Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "tower[" I "]" => BlowupTower.snoc BlowupTower.nil I
local notation "rays[" Δ "]" => Set.range (Fan.Ray.primitiveGenerator (Phi := Δ))
local notation "S" => Spec (CommRingCat.of ℂ)

variable (σ : Φ.cones)

local notation "p" => Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] n Y}

private theorem section_coefficients_of_absent_corner
    {Ψ F : Fan i} (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hF : F.IsRegular)
    (hN : finrank ℤ N = 2) (τ : Ψ.cones)
    (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    (ρ : Φ.Ray) (ρ' : Ψ.Ray) (hρ : ρ.primitiveGenerator = ρ'.primitiveGenerator)
    (hρ' : ¬ ρ'.toCone ≤ τ)
    (g : X[F] ≅ (I[σ]).blowup) (g' : X[F] ≅ (I[τ]).blowup)
    (hg : g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap)
    (hg' : g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap)
    (hT : IsClosedPointTower X[Φ] T) {q : Y} (hq : IsClosed ({q} : Set Y))
    (hA : (I[σ]).comap T.toBase = (Y.fromSpecResidueField q).ker)
    {W Z : Scheme} {L : BlowupTower (I[σ]).blowup n W}
    {U : BlowupTower (I[τ]).blowup n Z}
    (hL : IsClosedPointTower (I[σ]).blowup L) (hU : IsClosedPointTower (I[τ]).blowup U)
    (hτ : IsClosedPointTower X[Ψ] (tower[I[τ]]))
    (f : ((I[σ]).comap T.toBase).blowup ≅ W) {k : W ≅ Z}
    (hbase : f.hom ≫ L.toBase ≫ (I[σ]).blowupToBase =
      ((I[σ]).comap T.toBase).blowupToBase ≫ T.toBase)
    (hpic : ∀ x : Fin n → ℤ,
      pullback (f.inv ≫ ((I[σ]).comap T.toBase).blowupToBase) (T.picardHom (0, x)).toMul =
        ((tower[I[σ]].append L).picardHom (0, Fin.addCases (fun _ : Fin 1 ↦ 0) x)).toMul)
    (hlift : IsLift (g.symm ≪≫ g') L U k) :
    (hτ.append hU).strictTransformCoefficients (Ψ.rayBoundaryIdeal hΨ ρ') =
      Fin.addCases (fun _ : Fin 1 ↦ 0)
        (hT.strictTransformCoefficients (Φ.rayBoundaryIdeal hΦ ρ)) := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    rw [Fan.algebraicRealization_over]
    exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType (X[Φ] ↘ S)
  let : TauCeti.AlgebraicGeometry.IsRegular (Φ.rayBoundaryIdeal hΦ ρ).subscheme :=
    Φ.isRegular_rayBoundary hΦ ρ
  have hdim : topologicalKrullDim (Φ.rayBoundaryIdeal hΦ ρ).subscheme = 1 := by
    rw [Φ.rayBoundaryIdeal_def hΦ ρ]
    exact QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X[Φ] ↘ S) (n := 2)) _
  have hp := Φ.isClosed_singleton_distinguishedPoint σ
  have hleft := hT.strictTransformCoefficients_tail_prepend (X[Φ] ↘ S)
    hp (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField hq hA hL f hbase hpic
    (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ) hdim
  have hσ : IsClosedPointTower X[Φ] (tower[I[σ]]) :=
    .snoc .nil _ hp (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have hsrc : g.inv ≫ s.toFanHom.algebraicMap = (tower[I[σ]]).toBase := by
    rw [← hg, Iso.inv_hom_id_assoc, toBase_snoc, toBase_nil, Category.comp_id]
  have htgt : g.inv ≫ t.toFanHom.algebraicMap = (g.symm ≪≫ g').hom ≫ (tower[I[τ]]).toBase := by
    simp only [← hg', Iso.trans_hom, Iso.symm_hom, toBase_snoc, toBase_nil, Category.comp_id,
      Category.assoc]
  have hcurve := s.comap_strictTransform_rayBoundaryIdeal t hΦ hΨ hF hN
    hσ hτ g.inv (g.symm ≪≫ g') hsrc htgt ρ ρ' hρ
  have htail := hlift.strictTransformCoefficients_eq hL hU
    (tower[I[τ]].strictTransform (Ψ.rayBoundaryIdeal hΨ ρ'))
  rw [hcurve] at htail
  funext j
  refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) j
  · classical
    have ha : a = Fin.last 0 := Fin.ext (by omega)
    rw [Fin.addCases_left, strictTransformCoefficients_append_castAdd hτ hU, ha,
      strictTransformCoefficients_snoc_last _ _ _ (Ψ.isClosed_singleton_distinguishedPoint τ)
        (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField,
      strictTransform_nil, Ψ.stalkOrder_rayBoundaryIdeal_distinguishedPoint hΨ,
      ite_eq_right hρ']
    rfl
  · rw [Fin.addCases_right, strictTransformCoefficients_append_natAdd hτ hU,
      ← htail, strictTransform_snoc, strictTransform_nil, hleft]

/-- Transport a specified closed-point resolution across the toric Hirzebruch link
at a corner absent from its projected centers. The common resolution is obtained by
blowing up the inverse image of the corner. The two star subdivision maps send
each retained center on the intermediate model to its projections on both bases.
These centers keep their ruling values for every character ruling common to the
two fans. The first center of the new tower is the reverse corner over the ruling
value of the original corner.

In the two Picard markings the source coefficients `(a, b)` become `(a + b, b)`.
The new first exceptional coefficient is `-b`, and all old coefficients retain their
order, including those at infinitely near points. The strict section also retains its
old coefficients, with coefficient zero at the reverse corner. Taking a negative
signed parameter moves the Hirzebruch index down by one while preserving the ruling
fiber degree. -/
theorem exists_hirzebruch_toric_link_resolution_of_absent_corner
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, e • b 0 - b 1})
    (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
    (hT : IsClosedPointTower X[Φ] T) (hp : p ∉ Set.range hT.baseCenter) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    let A := (I[σ]).comap T.toBase
    ∃ (q : Y) (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (_ : F.IsRegular) (hc' : Ψ.IsComplete)
      (d : Basis (Fin 2) ℤ N) (τ : Ψ.cones) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
      (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
      (hr' : (fun j ↦ (r' j).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1])
      (g : X[F] ≅ (I[σ]).blowup) (g' : X[F] ≅ (I[τ]).blowup)
      (Z : Scheme) (U : BlowupTower (I[τ]).blowup n Z) (k : A.blowup ≅ Z)
      (hU : IsClosedPointTower (I[τ]).blowup U),
      let U' := (tower[I[τ]]).append U
      ∃ hU' : IsClosedPointTower X[Ψ] U',
      IsClosed ({q} : Set Y) ∧ T.toBase q = p ∧ A = (Y.fromSpecResidueField q).ker ∧
      d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧ τ.val = hull ℝ {i (d 1), i (-d 0)} ∧
      g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap ∧
      g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap ∧
      Φ.IsTwoRayStarSubdivision F ∧ Ψ.IsTwoRayStarSubdivision F ∧
      k.hom ≫ U.toBase ≫ g'.inv ≫ s.toFanHom.algebraicMap = A.blowupToBase ≫ T.toBase ∧
      k.hom ≫ U.toBase ≫ g'.inv ≫ t.toFanHom.algebraicMap = k.hom ≫ U'.toBase ∧
      (∀ j, s.toFanHom.algebraicMap (g'.inv (hU.baseCenter j)) = hT.baseCenter j) ∧
      hU'.baseCenter (Fin.castAdd n (0 : Fin 1)) =
        Ψ.distinguishedPointHom τ (IsLocalRing.closedPoint ℂ) ∧
      (∀ j : Fin n, t.toFanHom.algebraicMap (g'.inv (hU.baseCenter j)) =
        hU'.baseCenter (j.natAdd 1)) ∧
      (∀ (h₀ : ∀ γ : Φ.cones, (∀ x ∈ γ.val, 0 ≤ Φ.lattice.realCharacter
        (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
          Φ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0)
        (h₁ : ∀ γ : Ψ.cones, (∀ x ∈ γ.val, 0 ≤ Ψ.lattice.realCharacter
          (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
            Ψ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0),
        Ψ.characterRuling (b.coord 1).toAddMonoidHom h₁
            (hU'.baseCenter (Fin.castAdd n (0 : Fin 1))) =
          Φ.characterRuling (b.coord 1).toAddMonoidHom h₀ p) ∧
      (∀ (m : N →+ ℤ)
        (h₀ : ∀ γ : Φ.cones, (∀ x ∈ γ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
          ∀ x ∈ γ.val, Φ.lattice.realCharacter m x ≤ 0)
        (h₁ : ∀ γ : Ψ.cones, (∀ x ∈ γ.val, 0 ≤ Ψ.lattice.realCharacter m x) ∨
          ∀ x ∈ γ.val, Ψ.lattice.realCharacter m x ≤ 0) (j : Fin n),
        Ψ.characterRuling m h₁ (hU'.baseCenter (j.natAdd 1)) =
          Φ.characterRuling m h₀ (hT.baseCenter j)) ∧
      hU'.strictTransformCoefficients (Ψ.rayBoundaryIdeal hΨ (r' 0)) =
        Fin.addCases (fun _ : Fin 1 ↦ 0)
          (hT.strictTransformCoefficients (Φ.rayBoundaryIdeal hΦ (r 0))) ∧
      letI : Nonempty Ψ.cones := hc'.nonempty_cones
      let C := Fan.hirzebruchPicardBasis b e hΦ r hr
      let C' := Fan.hirzebruchPicardBasis d (e + 1) hΨ r' hr'
      ∀ (a β : ℤ) (m : Fin n → ℤ),
        pullback k.inv (pullback A.blowupToBase (T.picardHom (a • C 0 + β • C 1, m)).toMul) =
          (U'.picardHom ((a + β) • C' 0 + β • C' 1,
            Fin.addCases (fun _ : Fin 1 ↦ -β) m)).toMul := by
  intro A
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hI := (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have hinsert :=
    hT.exists_prepend_closed_point_blowup (Φ.isClosed_singleton_distinguishedPoint σ) hp
  rw [← hI] at hinsert
  obtain ⟨q, W, L, f, hL, hq, hqp, hA, hf, hcenters, hprep⟩ := hinsert
  obtain ⟨Ψ, F, hΨ, hF, hc', _, d, τ, s, t, g, g', r, r', hr, hr',
      hd₀, hd₁, hτ, hg, hg', hstar, hstar', -, hcoord⟩ :=
    Fan.exists_hirzebruch_toric_elementary_transform_picard_coordinates b e hΦ hc hrays σ hσ
  let R := L.transport (g.symm ≪≫ g')
  let hU : IsClosedPointTower (I[τ]).blowup R.tower := R.isLift.isClosedPointTower hL
  let k := f ≪≫ R.iso
  -- The reshaped tower starts at the reverse corner and then follows the transported tail.
  have hτTower : IsClosedPointTower X[Ψ] (tower[I[τ]]) :=
    .snoc .nil _ (Ψ.isClosed_singleton_distinguishedPoint τ)
      (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField
  have hsource : (g.symm ≪≫ g').hom ≫ g'.inv ≫ s.toFanHom.algebraicMap =
      (I[σ]).blowupToBase := by
    simp only [Iso.trans_hom, Iso.symm_hom, ← hg, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  have hpts (j : Fin n) :
      s.toFanHom.algebraicMap (g'.inv (hU.baseCenter j)) = hT.baseCenter j := by
    rw [← R.isLift.hom_baseCenter hL hU, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      hsource, hcenters j]
  have htarget : g'.inv ≫ t.toFanHom.algebraicMap = (I[τ]).blowupToBase := by
    rw [← hg', Iso.inv_hom_id_assoc]
  have hfirst : (hτTower.append hU).baseCenter (Fin.castAdd n (0 : Fin 1)) =
      Ψ.distinguishedPointHom τ (IsLocalRing.closedPoint ℂ) := by
    rw [baseCenter_append_castAdd hτTower hU, baseCenter_snoc_nil,
      hτTower.lastCenter_eq _ (Ψ.isClosed_singleton_distinguishedPoint τ)
        (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField]
  have htail (j : Fin n) : t.toFanHom.algebraicMap (g'.inv (hU.baseCenter j)) =
      (hτTower.append hU).baseCenter (j.natAdd 1) := by
    rw [← Scheme.Hom.comp_apply, htarget, baseCenter_append_natAdd hτTower hU]
    simp only [toBase_snoc, toBase_nil, Category.comp_id]
  refine ⟨q, Ψ, F, hΨ, hF, hc', d, τ, s, t, r, r', hr, hr', g, g', _, R.tower, k, hU,
    hτTower.append hU, hq, hqp, hA, hd₀, hd₁, hτ, hg, hg', hstar, hstar',
    ?_, ?_, hpts, hfirst, htail, ?_, ?_, ?_, ?_⟩
  · calc
      _ = f.hom ≫ (R.iso.hom ≫ R.tower.toBase) ≫ g'.inv ≫ s.toFanHom.algebraicMap := by
        simp only [k, Iso.trans_hom, Category.assoc]
      _ = _ := by rw [R.isLift.hom_toBase, Category.assoc L.toBase, hsource, hf]
  · simp only [toBase_append, toBase_snoc, toBase_nil, Category.comp_id, htarget]
  · intro h₀ h₁
    rw [hfirst]
    exact (Fan.characterRuling_distinguishedPointHom_eq_of_hirzebruch_link
      b d hd₀ hd₁ σ τ hσ hτ h₀ h₁ (IsLocalRing.closedPoint ℂ)).symm
  · intro m h₀ h₁ j
    have hpoint := congrArg (fun f : X[F] ⟶ projectiveLine ℂ ↦ f (g'.inv (hU.baseCenter j)))
      (s.comp_characterRuling_eq t m h₀ h₁)
    simpa only [Scheme.Hom.comp_apply, hpts j, htail j] using hpoint.symm
  · have hρ := (congrFun hr 0).trans (hd₀.symm.trans (congrFun hr' 0).symm)
    have hρ' := (r' 0).not_toCone_le_hirzebruch_reverse_corner d τ hτ (congrFun hr' 0)
    exact section_coefficients_of_absent_corner σ hΦ hΨ hF
      ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) τ s t
      (r 0) (r' 0) hρ hρ' g g' hg hg' hT hq hA hL hU hτTower f hf (hprep 0) R.isLift
  · intro C C' a β m
    have h := congrArg (pullback g'.inv) (hcoord a β 0)
    simp only [add_zero, sub_zero, pullback_comp, Iso.inv_hom_id, pullback_id] at h
    simp only [k, Iso.trans_inv]
    rw [← pullback_comp R.iso.inv f.inv, pullback_comp f.inv, hprep]
    simp only [picardHom_append, Fin.addCases_left, Fin.addCases_right]
    have hLift := R.isLift.symm.pullback_picardHom
      ((tower[I[σ]]).picardHom (a • C 0 + β • C 1, fun _ ↦ 0)) m
    simp only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv] at hLift
    rw [hLift, h, ofMul_toMul]

end QPainleve.BlowupTower.IsClosedPointTower

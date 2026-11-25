/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Hirzebruch

import Mathlib.Tactic.Module
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Picard
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback

/-!
# Picard coordinates of a toric Hirzebruch link

At a toric corner on the chosen section, blow up the corner and then contract
the strict transform of its fiber. In the basis given by the fiber and the
chosen section, a resolved class with coefficients `a, b, -m` acquires
coefficients `a + b - m, b, -(b - m)`. The signed Hirzebruch parameter
increases by one, so the same formula applies at either section.

This is the toric link in Lemma 8.9 and Proposition 8.11 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ F : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "R[" h "," ρ "]" => Fan.rayDivisorToPicard _ h (Pi.single ρ 1)
local notation "pb[" f "]" => AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (pullbackHom f))
local notation "tower[" I "]" => BlowupTower.snoc BlowupTower.nil I

open Classical in
private theorem exceptionalClass_eq_rayClass
    [Nonempty F.cones] (hF : F.IsRegular)
    {I : (X[Φ]).IdealSheafData} (g : X[F] ≅ I.blowup) (ρ : F.Ray)
    (h : (I.comap I.blowupToBase).comap g.hom = F.rayBoundaryIdeal hF ρ) :
    Additive.ofMul (pullback g.hom I.blowupExceptionalClass) = R[hF, ρ] := by
  let := F.uniqueFactorizationMonoid_stalk_algebraicRealization hF
  rw [rayDivisorToPicard_single, one_smul, primeDivisorClass_def]
  apply congrArg Additive.ofMul
  have hCartier : ((I.comap I.blowupToBase).comap g.hom).IsEffectiveCartier :=
    h.symm ▸ F.isEffectiveCartier_rayBoundaryIdeal hF ρ
  rw [blowupExceptionalClass_def, pullback_inv,
    I.isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf
      hCartier,
    mk_toInvertibleSheaf_congr _ _ (h.trans (F.rayBoundaryIdeal_def hF ρ))]

/-- The reverse corner, spanned by the fiber ray and the opposite section
ray, is disjoint from the section with generator `d 0`. -/
theorem Ray.not_toCone_le_hirzebruch_reverse_corner (ρ : Ψ.Ray) (d : Basis (Fin 2) ℤ N)
    (τ : Ψ.cones) (ht : τ.val = hull ℝ {i (d 1), i (-d 0)})
    (hρ : ρ.primitiveGenerator = d 0) : ¬ ρ.toCone ≤ τ := by
  intro h
  have hp := (ρ.toCone_le_iff τ).mp h
  rw [hρ] at hp
  have hn : -i (d 0) ∈ τ.val := by
    rw [← map_neg, ht]
    exact subset_hull (by simp)
  exact (Ψ.isToricCone τ.property).salient _ hp
    (fun hzero ↦ d.ne_zero 0 (Ψ.lattice.injective (hzero.trans (map_zero i).symm))) hn

private theorem hirzebruchLink_cornerMembership (b d : Basis (Fin 2) ℤ N)
    (σ : Φ.cones) (τ : Ψ.cones) (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
    (hs : σ.val = hull ℝ (Set.range (i ∘ b)))
    (ht : τ.val = hull ℝ {i (d 1), i (-d 0)})
    (hr₀ : (r 0).primitiveGenerator = b 0) (hr₁ : (r 1).primitiveGenerator = b 1)
    (hr'₀ : (r' 0).primitiveGenerator = d 0) (hr'₁ : (r' 1).primitiveGenerator = d 1) :
    (r 0).toCone ≤ σ ∧ (r 1).toCone ≤ σ ∧ (r' 1).toCone ≤ τ ∧ ¬ (r' 0).toCone ≤ τ := by
  refine ⟨((r 0).toCone_le_iff σ).mpr ?_, ((r 1).toCone_le_iff σ).mpr ?_,
    ((r' 1).toCone_le_iff τ).mpr ?_, (r' 0).not_toCone_le_hirzebruch_reverse_corner d τ ht hr'₀⟩
  · rw [hr₀, hs]
    exact subset_hull (Set.mem_range_self (0 : Fin 2))
  · rw [hr₁, hs]
    exact subset_hull (Set.mem_range_self (1 : Fin 2))
  · rw [hr'₁, ht]
    exact subset_hull (by simp)

private theorem hirzebruchLink_pullback_classes
    [Nonempty Φ.cones] [Nonempty Ψ.cones] [Nonempty F.cones]
    (b d : Basis (Fin 2) ℤ N) (e : ℤ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hF : F.IsRegular)
    (σ : Φ.cones) (τ : Ψ.cones) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    (g : X[F] ≅ (I[σ]).blowup) (g' : X[F] ≅ (I[τ]).blowup)
    (a : F.Ray) (f : Φ.Ray)
    (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
    (hr' : (fun j ↦ (r' j).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1])
    (hs : σ.val = hull ℝ (Set.range (i ∘ b))) (ht : τ.val = hull ℝ {i (d 1), i (-d 0)})
    (hd₀ : d 0 = b 0) (hd₁ : d 1 = b 0 + b 1)
    (ha : a.primitiveGenerator = b 0 + b 1) (hf : f.primitiveGenerator = b 1)
    (hg : g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap)
    (hg' : g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap)
    (hE : (I[σ]).comap s.toFanHom.algebraicMap = F.rayBoundaryIdeal hF a)
    (hE' : (I[τ]).comap t.toFanHom.algebraicMap = F.rayBoundaryIdeal hF (s.liftRay f)) :
    let C := hirzebruchPicardBasis b e hΦ r hr
    let C' := hirzebruchPicardBasis d (e + 1) hΨ r' hr'
    let E := Additive.ofMul (pullback g.hom (I[σ]).blowupExceptionalClass)
    let E' := Additive.ofMul (pullback g'.hom (I[τ]).blowupExceptionalClass)
    pb[s.toFanHom.algebraicMap] (C 0) = E + E' ∧
      pb[t.toFanHom.algebraicMap] (C' 0) = E + E' ∧
      pb[s.toFanHom.algebraicMap] (C 1) = pb[t.toFanHom.algebraicMap] (C' 1) + E := by
  classical
  dsimp only
  have hr₀ : (r 0).primitiveGenerator = b 0 := congrFun hr 0
  have hr₁ : (r 1).primitiveGenerator = b 1 := congrFun hr 1
  have hr'₀ : (r' 0).primitiveGenerator = d 0 := congrFun hr' 0
  have hr'₁ : (r' 1).primitiveGenerator = d 1 := congrFun hr' 1
  obtain ⟨h₀, h₁, h'₁, h'₀⟩ :=
    hirzebruchLink_cornerMembership b d σ τ r r' hs ht hr₀ hr₁ hr'₀ hr'₁
  have hN : finrank ℤ N = 2 := by simpa using finrank_eq_card_basis b
  have hsrc (j : Fin 4) := s.pullback_rayDivisorToPicard_single_of_pointBlowup hΦ hF hN σ (r j) g hg
  have htgt (j : Fin 4) :=
    t.pullback_rayDivisorToPicard_single_of_pointBlowup hΨ hF hN τ (r' j) g' hg'
  have he := exceptionalClass_eq_rayClass hF g a (by rwa [← comap_comp, hg])
  have he' := exceptionalClass_eq_rayClass hF g' (s.liftRay f) (by rwa [← comap_comp, hg'])
  have hF₁ : s.liftRay (r 1) = s.liftRay f := congrArg s.liftRay
    (Ray.primitiveGenerator_injective (hr₁.trans hf.symm))
  have hF'₁ : t.liftRay (r' 1) = a := Ray.primitiveGenerator_injective (by
    rw [t.primitiveGenerator_liftRay, hr'₁, hd₁, ha])
  have hF₀ : s.liftRay (r 0) = t.liftRay (r' 0) := Ray.primitiveGenerator_injective (by
    rw [s.primitiveGenerator_liftRay, t.primitiveGenerator_liftRay, hr₀, hr'₀, hd₀])
  simp only [hirzebruchPicardBasis_apply_zero, hirzebruchPicardBasis_apply_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsrc, ite_eq_left h₁, one_zsmul, hF₁, ← he', add_comm]
  · rw [htgt, ite_eq_left h'₁, one_zsmul, hF'₁, ← he]
  · rw [hsrc, htgt, ite_eq_left h₀, ite_eq_right h'₀, one_zsmul, zero_zsmul, add_zero, hF₀]

local notation "rays[" Δ "]" => Set.range (Ray.primitiveGenerator (Phi := Δ))

/-- A toric elementary link at the specified corner compares the two point
blowup markings on the same surface. With source coefficients `(a, b, c)`
in the fiber, section and exceptional classes, the target coefficients are
`(a + b + c, b, -b - c)`. The source and target morphisms are the toric
subdivision maps. -/
theorem exists_hirzebruch_toric_elementary_transform_picard_coordinates
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, e • b 0 - b 1})
    (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b))) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (hF : F.IsRegular)
      (hc' : Ψ.IsComplete) (_ : F.IsComplete) (d : Basis (Fin 2) ℤ N)
      (τ : Ψ.cones) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
      (g : X[F] ≅ (I[σ]).blowup) (g' : X[F] ≅ (I[τ]).blowup)
      (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
      (hr' : (fun j ↦ (r' j).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1]),
      d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧ τ.val = hull ℝ {i (d 1), i (-d 0)} ∧
      g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap ∧
      g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap ∧
      Φ.IsTwoRayStarSubdivision F ∧ Ψ.IsTwoRayStarSubdivision F ∧
      (I[τ]).comap t.toFanHom.algebraicMap = F.rayBoundaryIdeal hF (s.liftRay (r 1)) ∧
      letI : Nonempty Ψ.cones := hc'.nonempty_cones
      let C := hirzebruchPicardBasis b e hΦ r hr
      let C' := hirzebruchPicardBasis d (e + 1) hΨ r' hr'
      ∀ a b₀ c : ℤ,
        pullback g.hom ((tower[I[σ]]).picardHom (a • C 0 + b₀ • C 1, fun _ ↦ c)).toMul =
          pullback g'.hom ((tower[I[τ]]).picardHom
            ((a + b₀ + c) • C' 0 + b₀ • C' 1, fun _ ↦ -b₀ - c)).toMul := by
  obtain ⟨Ψ, F, hΨ, hF, hc', hcF, d, σ', τ, s, t, g, g', a, f,
    hσ', hd₀, hd₁, hrays', ha, hf, hg, hg', hE, hE', -, -, -, hstar, hstar', hτ⟩ :=
    exists_blowup_span_hirzebruch_toric_elementary_transformation b hΦ hc e hrays
  have hsame : σ' = σ := Subtype.ext (hσ'.trans hσ.symm)
  subst σ'
  obtain ⟨r, hr⟩ := exists_rayEquiv_of_hirzebruch_ray_generators b e hrays
  obtain ⟨r', hr'⟩ := exists_rayEquiv_of_hirzebruch_ray_generators d (e + 1) hrays'
  let := hc.nonempty_cones
  let := hc'.nonempty_cones
  let := hcF.nonempty_cones
  have hf' : f = r 1 := Ray.primitiveGenerator_injective (hf.trans (congrFun hr 1).symm)
  refine ⟨Ψ, F, hΨ, hF, hc', hcF, d, τ, s, t, g, g', r, r', hr, hr',
    hd₀, hd₁, hτ, hg, hg', hstar, hstar', hf' ▸ hE', fun α β c ↦ ?_⟩
  obtain ⟨hs, ht, hst⟩ := hirzebruchLink_pullback_classes b d e hΦ hΨ hF σ τ s t g g' a f
    r r' hr hr' hσ hτ hd₀ hd₁ ha hf hg hg' hE hE'
  apply Additive.ofMul.injective
  simp only [picardHom_snoc_apply_toMul, picardHom_nil, pullback_mul, pullback_comp, hg, hg',
    pullback_zpow, ofMul_mul, ofMul_zpow]
  have hpb {A B : Scheme} (f : A ⟶ B) (L : Additive (LineBundleClass B)) :
      Additive.ofMul (pullback f L.toMul) = pb[f] L := by
    simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, pullbackHom_apply]
  rw [hpb s.toFanHom.algebraicMap, hpb t.toFanHom.algebraicMap]
  simp only [map_add, map_zsmul, hs, ht, hst]
  module

end TauCeti.Toric.Fan

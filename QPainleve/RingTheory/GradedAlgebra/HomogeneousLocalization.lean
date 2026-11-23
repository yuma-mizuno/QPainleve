/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Transport of standard graded localizations

A bijective graded ring homomorphism induces a bijection on the degree-zero localizations
used for the standard affine charts of a projective spectrum.
-/

public section

namespace HomogeneousLocalization.Away

variable {ι A B σ τ : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A bijective graded ring map induces a bijection on the standard localization
at a homogeneous element. -/
theorem map_bijective {g : 𝒜 →+*ᵍ ℬ} (hg : Function.Bijective g) {f : A} {d : ι}
    (hf : f ∈ 𝒜 d) : Function.Bijective (Away.map g f) := by
  have : IsLocalization ((Submonoid.powers f).map g.toRingHom) (Localization.Away (g f)) := by
    rw [Submonoid.map_powers]
    infer_instance
  have hinj := IsLocalization.map_injective_of_injective (Submonoid.powers f)
    (Localization.Away f) (Localization.Away (g f)) (g := g.toRingHom) hg.injective
  have hval (x : Away 𝒜 f) :
      (Away.map g f x).val =
        IsLocalization.map (Localization.Away (g f)) g.toRingHom
          (Submonoid.powers f).le_comap_map x.val := by
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
    simp [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  refine ⟨fun x y h ↦ val_injective _ (hinj ?_), Away.map_surjective hg.surjective hf⟩
  rw [← hval x, ← hval y, h]

/-- Transporting the localization at a homogeneous element along an equality
transports the denominator of every homogeneous fraction. -/
theorem cast_mk {f g : A} (h : f = g) {d : ι} (hf : f ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    RingEquiv.cast (R := Away 𝒜) h (Away.mk 𝒜 hf n a ha) =
      Away.mk 𝒜 (h ▸ hf) n a ha := by
  subst g
  rfl

end HomogeneousLocalization.Away

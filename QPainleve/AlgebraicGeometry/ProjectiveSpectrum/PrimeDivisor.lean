/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Prime homogeneous elements and projective divisors

If a positive-degree homogeneous prime generates a relevant ideal, that ideal is the
unique codimension-one point of the complement of its standard open. This identifies the
prime divisor in projective Picard excision. The codimension comparison uses the
comparison of chains in Tau Ceti's `Proj.coheight_add_one_le_ringKrullDim`.
-/

public section

open CategoryTheory TopologicalSpace Order

namespace AlgebraicGeometry.Proj

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The codimension of a point in the projective spectrum is bounded by the height of
its underlying prime in the homogeneous coordinate ring. -/
theorem coheight_le_height_asHomogeneousIdeal (x : Proj 𝒜) :
    coheight x ≤ x.asHomogeneousIdeal.toIdeal.height := by
  let f : Proj 𝒜 → (PrimeSpectrum A)ᵒᵈ := fun y ↦
    OrderDual.toDual ⟨y.asHomogeneousIdeal.toIdeal, y.isPrime⟩
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun y z hyz ↦ ?_) fun y z hyz ↦ ?_
    · exact (ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜 z y).mpr
        ((ProjectiveSpectrum.le_iff_mem_closure 𝒜 z y).mpr (specializes_iff_mem_closure.mp hyz))
    · exact ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
        (congrArg PrimeSpectrum.asIdeal (OrderDual.toDual.injective hyz)))
  have h := coheight_le_coheight_apply_of_strictMono f hf x
  exact h.trans_eq ((⟨_, x.isPrime⟩ : PrimeSpectrum A).height_eq_orderHeight.symm)

/-- The closed complement of the standard open of a homogeneous prime of positive
degree has a unique codimension-one point, provided the prime ideal is relevant. -/
theorem existsUnique_codimensionOnePoint_notMem_basicOpen [IsDomain A] [IsNoetherianRing A]
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hp : Prime f)
    (hrel : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span {f}) :
    ∃! x : TauCeti.AlgebraicGeometry.CodimensionOnePoint (Proj 𝒜),
      (x : Proj 𝒜) ∉ basicOpen 𝒜 f := by
  let η : Proj 𝒜 := ⟨⟨Ideal.span {f}, Ideal.isHomogeneous_span_singleton _ ⟨d, hf⟩⟩,
    Ideal.isPrime_span_singleton_of_prime hp, hrel⟩
  have hη : η ∉ basicOpen 𝒜 f := by
    rw [mem_basicOpen, not_not]
    exact Ideal.mem_span_singleton_self f
  have hR : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥ := by
    intro h
    have hm : f ∈ (⊥ : HomogeneousIdeal 𝒜) := h ▸ HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hf
    exact hp.ne_zero (by simpa only [← HomogeneousIdeal.mem_iff,
      HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] using hm)
  have : IsIntegral (Proj 𝒜) := isIntegral_of_isDomain 𝒜 hR
  have hU : (basicOpen 𝒜 f : Set (Proj 𝒜)).Nonempty := by
    let z : Proj 𝒜 := ⟨⊥, Ideal.isPrime_bot, fun h ↦ hR (le_bot_iff.mp h)⟩
    refine ⟨z, (mem_basicOpen 𝒜 f z).mpr ?_⟩
    simpa only [z, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
      using hp.ne_zero
  have hco : coheight η = 1 := by
    apply le_antisymm
    · exact (coheight_le_height_asHomogeneousIdeal η).trans_eq
        (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit)
    · have hpos : 0 < coheight η := by
        rw [coheight_pos, TauCeti.AlgebraicGeometry.Scheme.isMax_iff_eq_genericPoint]
        intro heq
        obtain ⟨z, hz⟩ := hU
        exact hη (heq ▸ (genericPoint_specializes z).mem_open (basicOpen 𝒜 f).isOpen hz)
      exact Order.one_le_iff_pos.mpr hpos
  refine ⟨⟨η, hco⟩, hη, fun x hx ↦ Subtype.ext ?_⟩
  have hle : η.asHomogeneousIdeal ≤ (x : Proj 𝒜).asHomogeneousIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (not_not.mp (mt (mem_basicOpen 𝒜 f x).mpr hx))
  have hspec : η ⤳ (x : Proj 𝒜) := specializes_iff_mem_closure.mpr
    ((ProjectiveSpectrum.le_iff_mem_closure 𝒜 η (x : Proj 𝒜)).mp
      ((ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜 η (x : Proj 𝒜)).mp hle))
  exact (TauCeti.AlgebraicGeometry.Scheme.eq_of_specializes_of_notMem hU x.property hspec hη).symm

end AlgebraicGeometry.Proj

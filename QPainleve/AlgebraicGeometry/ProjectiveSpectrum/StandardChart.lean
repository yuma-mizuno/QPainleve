/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
import QPainleve.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Dehomogenization

/-!
# Standard affine charts of projective space

In the projective spectrum of a symmetric algebra, the standard open given by a basis
vector has polynomial coordinate ring in the other basis vectors. This gives the dimension
and factoriality of the stalks over a field. The chart uses Mathlib's
`SymmetricAlgebra.equivMvPolynomial` and Tau Ceti's `HomogeneousIdeal.awayEquivDehomogenize`.

See the Stacks Project, Section 27.13 (tag 01ND).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Topology

namespace Module.Basis

attribute [local instance] MvPolynomial.gradedAlgebra

open TauCeti.SymmetricAlgebra

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule R M
local notation "coord" => fun (b : Basis (Fin (n + 1)) R M) i ↦ SymmetricAlgebra.ι R M (b i)

private noncomputable abbrev zeroPolynomialIdeal :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
  ⊥

private noncomputable def gradedPolynomialQuotient (b : Basis (Fin (n + 1)) R M) :
    𝒜 →+*ᵍ (zeroPolynomialIdeal (R := R) (n := n)).quotientGrading where
  __ := (Ideal.Quotient.mk ⊥).comp (SymmetricAlgebra.equivMvPolynomial b).toRingHom
  map_mem {j} {f} hf :=
    TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
      ((SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b j f).mpr hf)

private theorem gradedPolynomialQuotient_bijective (b : Basis (Fin (n + 1)) R M) :
    Function.Bijective (gradedPolynomialQuotient b) :=
  (RingEquiv.quotientBot _).symm.bijective.comp (SymmetricAlgebra.equivMvPolynomial b).bijective

private theorem gradedPolynomialQuotient_coord (b : Basis (Fin (n + 1)) R M) (i : Fin (n + 1)) :
    gradedPolynomialQuotient b (coord b i) = Ideal.Quotient.mk ⊥ (MvPolynomial.X i) := by
  simp [gradedPolynomialQuotient]

/-- The standard chart ring at the coordinate indexed by `i` is the polynomial ring
on the other `n` coordinates, ordered by `Fin.succAbove i`. -/
noncomputable def awayEquivMvPolynomial (b : Basis (Fin (n + 1)) R M) (i : Fin (n + 1)) :
    Away 𝒜 (coord b i) ≃+* MvPolynomial (Fin n) R := by
  let I := zeroPolynomialIdeal (R := R) (n := n)
  let e := RingEquiv.ofBijective (Away.map (gradedPolynomialQuotient b) (coord b i))
    (Away.map_bijective (gradedPolynomialQuotient_bijective b)
      (ι_mem_homogeneousSubmodule R M (b i)))
  exact (e.trans (RingEquiv.cast (R := Away I.quotientGrading)
      (gradedPolynomialQuotient_coord b i))).trans
    ((I.awayEquivDehomogenize i).toRingEquiv.trans
      ((Ideal.quotEquivOfEq (R := MvPolynomial (Fin n) R) (Ideal.map_bot)).trans
        (RingEquiv.quotientBot _)))

/-- On a fraction in the chart, the polynomial identification sets the chosen
homogeneous coordinate to one. -/
@[simp]
theorem awayEquivMvPolynomial_mk (b : Basis (Fin (n + 1)) R M) (i : Fin (n + 1))
    (m : ℕ) (p : SymmetricAlgebra R M) (hp : p ∈ 𝒜 (m • 1)) :
    b.awayEquivMvPolynomial i (Away.mk 𝒜 (ι_mem_homogeneousSubmodule R M (b i)) m p hp) =
      TauCeti.dehomogenize i (SymmetricAlgebra.equivMvPolynomial b p) := by
  simp only [awayEquivMvPolynomial, RingEquiv.trans_apply, RingEquiv.ofBijective_apply,
    Away.map_mk, Away.cast_mk]
  let I := zeroPolynomialIdeal (R := R) (n := n)
  have hp' : Ideal.Quotient.mk I.toIdeal (SymmetricAlgebra.equivMvPolynomial b p) ∈
      I.quotientGrading (m • 1) := (gradedPolynomialQuotient b).map_mem hp
  -- Align the transported denominator and its degree proof with the quotient chart.
  change (RingEquiv.quotientBot _)
      (Ideal.quotEquivOfEq (Ideal.map_bot)
        (I.awayEquivDehomogenize i
          (Away.mk I.quotientGrading (I.mk_X_mem_quotientGrading i) m _ hp'))) = _
  rw [I.awayEquivDehomogenize_mk i hp']
  let q := TauCeti.dehomogenize i (SymmetricAlgebra.equivMvPolynomial b p)
  have hbot : I.toIdeal.map (TauCeti.dehomogenize i) = ⊥ := Ideal.map_bot
  exact (congrArg (RingEquiv.quotientBot _) (Ideal.quotEquivOfEq_mk hbot q)).trans
    (RingEquiv.quotientBot_mk q)

private theorem exists_awayι_apply_eq (b : Basis (Fin (n + 1)) R M) (x : Proj 𝒜) :
    ∃ (i : Fin (n + 1)) (y : Spec (.of (Away 𝒜 (coord b i)))),
      Proj.awayι 𝒜 (coord b i) (ι_mem_homogeneousSubmodule R M (b i)) Nat.one_pos y = x := by
  have hcover := iSup_basicOpen_ι_eq_top R M b b.span_eq
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, Proj.basicOpen 𝒜 (coord b i) by rw [hcover]; trivial)
  rw [← Proj.opensRange_awayι 𝒜 _ (ι_mem_homogeneousSubmodule _ _ (b i)) Nat.one_pos] at hi
  exact ⟨i, hi⟩

/-- Projective space on a basis of `n + 1` elements over a field has dimension `n`. -/
theorem topologicalKrullDim_proj {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (b : Basis (Fin (n + 1)) k V) :
    topologicalKrullDim (Proj (homogeneousSubmodule k V)) = n := by
  let A := homogeneousSubmodule k V
  let c (i : Fin (n + 1)) := SymmetricAlgebra.ι k V (b i)
  let f (i : Fin (n + 1)) := Proj.awayι A (c i) (ι_mem_homogeneousSubmodule _ _ (b i)) Nat.one_pos
  have hdim (i : Fin (n + 1)) : topologicalKrullDim (Spec (.of (Away A (c i)))) = n := by
    calc
      _ = ringKrullDim (Away A (c i)) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ = ringKrullDim (MvPolynomial (Fin n) k) :=
        ringKrullDim_eq_of_ringEquiv (b.awayEquivMvPolynomial i)
      _ = n := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
        simp
  rw [TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding (fun i ↦ f i)
    (fun i ↦ (f i).isOpenEmbedding) (fun x ↦ b.exists_awayι_apply_eq x)]
  simp [hdim]

/-- The local rings of projective space over a unique factorization domain are factorial. -/
theorem uniqueFactorizationMonoid_stalk_proj [UniqueFactorizationMonoid R]
    (b : Basis (Fin (n + 1)) R M) (x : Proj 𝒜) :
    UniqueFactorizationMonoid ((Proj 𝒜).presheaf.stalk x) := by
  obtain ⟨i, y, rfl⟩ := b.exists_awayι_apply_eq x
  let f := Proj.awayι 𝒜 _ (ι_mem_homogeneousSubmodule _ _ (b i)) Nat.one_pos
  let S := CommRingCat.of (Away 𝒜 (coord b i))
  have : UniqueFactorizationMonoid S :=
    (b.awayEquivMvPolynomial i).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have : y.asIdeal.IsPrime := y.isPrime
  let : Algebra S ((Spec S).presheaf.stalk y) := StructureSheaf.stalkAlgebra S y
  have : IsLocalization.AtPrime ((Spec S).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk S y
  have h := UniqueFactorizationMonoid.of_isLocalization y.asIdeal.primeCompl
    ((Spec S).presheaf.stalk y)
  exact (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.symm
    |>.uniqueFactorizationMonoid h

end Module.Basis

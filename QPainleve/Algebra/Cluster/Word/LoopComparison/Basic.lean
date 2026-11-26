/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.Algebra.Cluster.Word.KernelMatrix.Computed

/-!
# Integer comparison of typed signed loops

The comparison uses the square matrix of the exchange-kernel pullback in the computed
integral basis and a supplied boundary order table.
It can be used with typed paths obtained from generator lists or from a toric presentation.
-/

public section

open Quiver

namespace QPainleve.Cluster.SkewExchangeMatrix

variable {r n : ℕ} [NeZero n] (B : SkewExchangeMatrix (Fin r))

/-- Compare two loops by inversion sign, their square matrices in the computed integral
exchange-kernel basis, and forward boundary label. Row zero supplies the initial boundary
orders. -/
def compareSignedLoops (orders : Fin n → Fin r → ℤ) (w v : Word B B) : Bool :=
  decide (((-1 : ℤˣ) ^ w.inversionCount = (-1 : ℤˣ) ^ v.inversionCount) ∧
    w.computedExchangeKernelMatrix = v.computedExchangeKernelMatrix ∧
    w.tropicalBoundaryLabel orders (orders 0) = v.tropicalBoundaryLabel orders (orders 0))

/-- The comparison returns true exactly when the three signed loop invariants agree. -/
@[simp]
theorem compareSignedLoops_eq_true_iff (orders : Fin n → Fin r → ℤ) (w v : Word B B) :
    B.compareSignedLoops orders w v = true ↔
      w.signedLoopInvariants B.matrix.intKernelBasisVectors.2 orders (orders 0) =
        v.signedLoopInvariants B.matrix.intKernelBasisVectors.2 orders (orders 0) := by
  rw [compareSignedLoops, decide_eq_true_eq, Path.computedExchangeKernelMatrix_eq_iff]
  simpa only [Matrix.intKernelBasis_apply] using
    (w.signedLoopInvariants_eq_iff v B.matrix.intKernelBasis orders orders (orders 0)).symm

/-- A relation criterion on integral kernel bases certifies the Boolean comparison, which
uses the basis computed from the exchange matrix. -/
theorem compareSignedLoops_eq_true_iff_xPullback_eq (k : Type*) [Field k]
    (orders : Fin n → Fin r → ℤ) (w v : Word B B)
    (criterion : ∀ {d : ℕ} (β : Module.Basis (Fin d) ℤ B.matrix.mulVecLin.ker),
      w.xPullback k = v.xPullback k ↔
        w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
          v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0)) :
    B.compareSignedLoops orders w v = true ↔ w.xPullback k = v.xPullback k := by
  simpa only [compareSignedLoops_eq_true_iff, Matrix.intKernelBasis_apply]
    using (criterion B.matrix.intKernelBasis).symm

end QPainleve.Cluster.SkewExchangeMatrix

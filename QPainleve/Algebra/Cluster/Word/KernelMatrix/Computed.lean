/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.KernelMatrix.Basic
public import QPainleve.LinearAlgebra.Matrix.Kernel.Basic

import QPainleve.Algebra.Cluster.Word.Monomial
import QPainleve.LinearAlgebra.Matrix.Array

/-!
# Computable matrices of exchange-kernel transport

The integral kernel algorithm supplies coordinate equivalences at both ends of a
word. Conjugating the exponent pullback by these equivalences computes its matrix
and gives the square matrix used for comparing signed loops. The product law uses
`LinearMap.toMatrix_comp` through `Quiver.Path.exchangeKernelMatrix_comp`.
-/

public section

open QPainleve.Cluster

namespace Quiver.Path

variable {r : ℕ} {B C D : SkewExchangeMatrix (Fin r)}

/-- The integer matrix of a word's exchange-kernel pullback, in the computed kernel
bases of its initial and terminal exchange matrices. Rows use the initial basis. -/
def computedExchangeKernelMatrix (w : Word B C) :
    Matrix (Fin B.matrix.intKernelBasisVectors.1) (Fin C.matrix.intKernelBasisVectors.1) ℤ :=
  let initial := B.matrix.intKernelBasisEquiv
  let terminal := C.matrix.intKernelBasisEquiv
  let pullback := terminal.symm.trans (w.exchangeKernelEquiv.trans initial)
  pullback.toLinearMap.materializeMatrix.val

/-- Each column gives the computed basis coordinates of a transported basis vector. -/
theorem computedExchangeKernelMatrix_apply (w : Word B C)
    (i : Fin B.matrix.intKernelBasisVectors.1) (j : Fin C.matrix.intKernelBasisVectors.1) :
    w.computedExchangeKernelMatrix i j =
      B.matrix.intKernelBasisEquiv (w.exchangeKernelEquiv
        (C.matrix.intKernelBasisEquiv.symm (Pi.single j 1))) i := by
  simp only [computedExchangeKernelMatrix, LinearMap.materializeMatrix_apply,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]

/-- The computed matrix represents the exchange-kernel pullback in the endpoint bases. -/
theorem computedExchangeKernelMatrix_eq (w : Word B C) :
    w.computedExchangeKernelMatrix =
      w.exchangeKernelMatrix B.matrix.intKernelBasis C.matrix.intKernelBasis := by
  ext i j
  rw [computedExchangeKernelMatrix_apply, exchangeKernelMatrix_apply,
    Matrix.intKernelBasisEquiv_symm_single, ← Matrix.intKernelBasis_equivFun,
    Module.Basis.equivFun_apply]

/-- Two computed matrices agree exactly when their exchange-kernel pullbacks agree. -/
theorem computedExchangeKernelMatrix_eq_iff (w v : Word B C) :
    w.computedExchangeKernelMatrix = v.computedExchangeKernelMatrix ↔
      w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
  simp only [computedExchangeKernelMatrix_eq, exchangeKernelMatrix_def, EquivLike.apply_eq_iff_eq,
    LinearEquiv.toLinearMap_inj]

/-- The empty word computes the identity matrix. -/
@[simp]
theorem computedExchangeKernelMatrix_nil :
    (Path.nil : Word B B).computedExchangeKernelMatrix = 1 := by
  rw [computedExchangeKernelMatrix_eq, exchangeKernelMatrix_nil]

/-- Concatenation multiplies the computed matrices in pullback order. -/
theorem computedExchangeKernelMatrix_comp (w : Word B C) (v : Word C D) :
    (w.comp v).computedExchangeKernelMatrix =
      w.computedExchangeKernelMatrix * v.computedExchangeKernelMatrix := by
  simp only [computedExchangeKernelMatrix_eq]
  exact w.exchangeKernelMatrix_comp v B.matrix.intKernelBasis C.matrix.intKernelBasis
    D.matrix.intKernelBasis

/-- Appending a step multiplies by its computed matrix on the right. -/
theorem computedExchangeKernelMatrix_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).computedExchangeKernelMatrix =
      w.computedExchangeKernelMatrix * s.toPath.computedExchangeKernelMatrix := by
  simp only [computedExchangeKernelMatrix_eq]
  exact w.exchangeKernelMatrix_cons s B.matrix.intKernelBasis C.matrix.intKernelBasis
    D.matrix.intKernelBasis

/-- Multiplying by the matrix of the reverse word recovers the identity. -/
@[simp]
theorem computedExchangeKernelMatrix_mul_reverse (w : Word B C) :
    w.computedExchangeKernelMatrix * w.reverse.computedExchangeKernelMatrix = 1 := by
  rw [← computedExchangeKernelMatrix_comp, ← computedExchangeKernelMatrix_nil (B := B),
    computedExchangeKernelMatrix_eq_iff]
  simp

end Quiver.Path

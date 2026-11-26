/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QPainleve.Algebra.Cluster.Word.Exponent

/-!
# Matrices of exchange-kernel transport

Choosing integer bases at the vertices of a cluster word represents its pullback on
exchange kernels by a product of edge matrices. The rows use the source basis and
the columns use the target basis, so adjoining a step multiplies its matrix on the right.
-/

public section

open Module QPainleve.Cluster

namespace Quiver.Path

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B C D : SkewExchangeMatrix ι}
  {α β γ : Type*}

local notation "K[" E "]" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))

/-- The matrix of the exponent pullback, with rows in the initial kernel basis
and columns in the terminal kernel basis. -/
noncomputable def exchangeKernelMatrix [Finite α] [Fintype β] [DecidableEq β]
    (w : Word B C) (b : Basis α ℤ K[B]) (c : Basis β ℤ K[C]) : Matrix α β ℤ :=
  LinearMap.toMatrix c b w.exchangeKernelEquiv.toLinearMap

/-- The exchange-kernel matrix is the `LinearMap.toMatrix` representation of the
word's kernel pullback. -/
theorem exchangeKernelMatrix_def [Finite α] [Fintype β] [DecidableEq β]
    (w : Word B C) (b : Basis α ℤ K[B]) (c : Basis β ℤ K[C]) :
    w.exchangeKernelMatrix b c = LinearMap.toMatrix c b w.exchangeKernelEquiv.toLinearMap := (rfl)

/-- The matrix column at `j` gives the coordinates of the transported basis vector `c j`. -/
theorem exchangeKernelMatrix_apply [Finite α] [Fintype β] [DecidableEq β]
    (w : Word B C) (b : Basis α ℤ K[B]) (c : Basis β ℤ K[C]) (i : α) (j : β) :
    w.exchangeKernelMatrix b c i j = b.repr (w.exchangeKernelEquiv (c j)) i :=
  LinearMap.toMatrix_apply c b _ i j

/-- The empty word has the identity matrix in a common source and target basis. -/
@[simp]
theorem exchangeKernelMatrix_nil [Fintype α] [DecidableEq α] (b : Basis α ℤ K[B]) :
    (Path.nil : Word B B).exchangeKernelMatrix b b = 1 := by
  simp [exchangeKernelMatrix, LinearMap.toMatrix_id]

/-- At an intermediate seed the same basis is used for both incident matrices.
The product transports exponents from the terminal seed back to the initial seed. -/
theorem exchangeKernelMatrix_comp [Finite α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (w : Word B C) (v : Word C D) (b : Basis α ℤ K[B]) (c : Basis β ℤ K[C])
    (d : Basis γ ℤ K[D]) :
    (w.comp v).exchangeKernelMatrix b d =
      w.exchangeKernelMatrix b c * v.exchangeKernelMatrix c d := by
  unfold exchangeKernelMatrix
  rw [exchangeKernelEquiv_comp, LinearEquiv.coe_trans, LinearMap.toMatrix_comp d c b]

/-- Appending one mutation, relabeling, or inversion multiplies by its edge matrix. -/
theorem exchangeKernelMatrix_cons [Finite α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (w : Word B C) (s : C ⟶ D) (b : Basis α ℤ K[B]) (c : Basis β ℤ K[C])
    (d : Basis γ ℤ K[D]) :
    (w.cons s).exchangeKernelMatrix b d =
      w.exchangeKernelMatrix b c * s.toPath.exchangeKernelMatrix c d := by
  simpa only [Hom.toPath, comp_cons, comp_nil] using w.exchangeKernelMatrix_comp s.toPath b c d

end Quiver.Path

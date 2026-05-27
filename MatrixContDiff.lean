/-
Bridge lemma: matrix-valued `ContDiff` ↔ entry-wise `ContDiff`.

Under the local `Matrix.linftyOpNormedAddCommGroup` instance, the standard
`contDiff_pi` does not fire on `Matrix m n ℝ` because the inner Pi
component carries `PiLp.normedAddCommGroupToPi 1` (rather than the
default `Pi.normedAddCommGroup`) and Lean's typeclass search can't
resolve the inner instance. We provide a single reusable equivalence by
transferring through the underlying Pi-Pi function type
`m → n → ℝ`, which `def Matrix m n α := m → n → α` makes definitionally
equal but instance-distinct from `Matrix m n ℝ`. The identity linear map
between the two is auto-continuous in finite dim, providing the bridge.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace Iwasawa.MatrixContDiff

open Matrix

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The identity as a `LinearEquiv` from `Matrix m n ℝ` (linftyOp norm in
scope) to the underlying Pi-Pi type `m → n → ℝ` (default Pi norm). -/
def matrixPiLE : Matrix m n ℝ ≃ₗ[ℝ] (m → n → ℝ) where
  toFun := fun M => M
  invFun := fun f => f
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- The identity as a `ContinuousLinearEquiv`, via finite-dim auto-continuity. -/
noncomputable def matrixPiCLE : Matrix m n ℝ ≃L[ℝ] (m → n → ℝ) :=
  matrixPiLE.toContinuousLinearEquiv

@[simp] lemma matrixPiCLE_apply (M : Matrix m n ℝ) :
    matrixPiCLE M = (M : m → n → ℝ) := rfl

@[simp] lemma matrixPiCLE_symm_apply (f : m → n → ℝ) :
    matrixPiCLE.symm f = (f : Matrix m n ℝ) := rfl

/-- The `(j, i)` entry of a matrix as a continuous linear functional on
`Matrix m n ℝ` (under the local `linftyOp` norm). -/
noncomputable def entryCLM (j : m) (i : n) :
    Matrix m n ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i : (n → ℝ) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.proj j : (m → n → ℝ) →L[ℝ] (n → ℝ)).comp
      matrixPiCLE.toContinuousLinearMap)

@[simp] lemma entryCLM_apply (j : m) (i : n) (M : Matrix m n ℝ) :
    entryCLM j i M = M j i := rfl

/-- A matrix-valued function is `ContDiffOn` iff each entry is `ContDiffOn`.
The reverse direction is the standard pi-aggregation, which `contDiffOn_pi`
provides only on the underlying Pi-Pi type `m → n → ℝ` (not directly on
`Matrix m n ℝ` under `linftyOp` norm); we bridge via `matrixPiCLE`. -/
lemma contDiffOn_matrix_iff_entries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Matrix m n ℝ} {s : Set E} {k : WithTop ℕ∞} :
    ContDiffOn ℝ k f s ↔ ∀ i j, ContDiffOn ℝ k (fun x => f x i j) s := by
  constructor
  · -- Forward: each entry is composition with a CLM (continuous in linftyOp).
    intro hf i j
    have h_pi : ContDiffOn ℝ k (fun x => matrixPiCLE (f x)) s := by
      have : ContDiffOn ℝ k (matrixPiCLE.toContinuousLinearMap ∘ f) s :=
        matrixPiCLE.contDiff.comp_contDiffOn hf
      exact this
    rw [contDiffOn_pi] at h_pi
    have hi := h_pi i
    rw [contDiffOn_pi] at hi
    exact hi j
  · -- Reverse: build `matrixPiCLE ∘ f` via contDiffOn_pi (Pi-Pi target).
    intro h
    have h_pi : ContDiffOn ℝ k (fun x => matrixPiCLE (f x)) s := by
      apply contDiffOn_pi.mpr; intro i
      apply contDiffOn_pi.mpr; intro j
      exact h i j
    -- Transfer back: `f = matrixPiCLE.symm ∘ (matrixPiCLE ∘ f)`.
    have h_eq : f = fun x => matrixPiCLE.symm (matrixPiCLE (f x)) := by
      ext x; simp
    rw [h_eq]
    exact matrixPiCLE.symm.contDiff.comp_contDiffOn h_pi

end Iwasawa.MatrixContDiff

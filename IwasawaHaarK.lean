/-
# IwasawaHaarK.lean

Level 1 (Route B): the Haar measure on `K n = O(n)` in Cayley coordinates.

This file develops the orthogonal-group factor of the Iwasawa integration
formula. The Cayley chart `cayleyToK : Sk n → K n` parameterizes the identity
component `SO(n)` (the locus where `1 + Q` is invertible) by skew-symmetric
matrices. Because `O(n)` is a curved group, flat Lebesgue measure on the chart
is NOT left invariant; the correct left invariant density is the Cayley
Jacobian density `ρK X ∝ |det (1 + X)|^{-(n-1)}`.

This first section (B1b') defines that density and PINS its exponent by an
honest determinant computation: the intrinsic derivative of the Cayley chart,
expressed as an endomorphism of the identity tangent space `Sk n`, is
`-2 • sandwichOnSkCLM ((1 + X)⁻¹)`, whose determinant is computed by the
already-proven `det_sandwichOnSkCLM`. The resulting exponent `-(n-1)` is read
off, not hard-coded, and the constant matches the `SO(2)` value `2/(1+a²)`.
-/

import iwasawa_change_of_coords.IwasawaHaar

namespace IwasawaCoC

open Matrix Iwasawa MeasureTheory
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace Complete

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-! ## B1b': the Cayley chart derivative on `Sk n` and its determinant -/

/-- **Intrinsic derivative of the Cayley chart at `X`.**

The ambient Fréchet derivative of `cayley` at a skew `X` is
`cayleyFDerivCLM X : δ ↦ -2 (1+X)⁻¹ δ (1+X)⁻¹`, which sends `Sk n` into the
tangent space `T_{cayley X} SO(n) = (cayley X) · Sk n`, not back into `Sk n`.
Translating that image back to the identity tangent space by left
multiplication by `(cayley X)⁻¹ = (cayley X)ᵀ` gives the genuine endomorphism
of `Sk n`
`δ ↦ -2 (1-X)⁻¹ δ (1+X)⁻¹`.
For skew `X` one has `((1+X)⁻¹)ᵀ = (1-X)⁻¹`, so this is exactly
`-2 • sandwichOnSkCLM ((1+X)⁻¹)` (recall `sandwichOnSkCLM B : δ ↦ Bᵀ δ B`). -/
noncomputable def cayleyDerivOnSk (X : Sk n) : Sk n →L[ℝ] Sk n :=
  (-2 : ℝ) • sandwichOnSkCLM ((1 + X.1)⁻¹)

/-- The value of `cayleyDerivOnSk` is the left-translated Cayley derivative
`δ ↦ -2 (1-X)⁻¹ δ (1+X)⁻¹`. -/
@[simp] lemma cayleyDerivOnSk_apply_val (X : Sk n) (δ : Sk n) :
    ((cayleyDerivOnSk X δ : Sk n) : Matrix (Fin n) (Fin n) ℝ)
      = (-2 : ℝ) • (((1 + X.1)⁻¹).transpose * δ.1 * (1 + X.1)⁻¹) := by
  rw [cayleyDerivOnSk]
  rw [ContinuousLinearMap.smul_apply, Submodule.coe_smul, sandwichOnSkCLM_apply_val]

/-- **B1b' determinant pin.** The intrinsic Cayley chart derivative on `Sk n`
has determinant `(-2)^{dim Sk} · (det (1+X))^{-(n-1)}`, where
`dim Sk = card (nnIndex n) = n(n-1)/2`. The exponent `-(n-1)` is read off from
`det_sandwichOnSkCLM` (the `(det B)^{n-1}` exterior-power identity), not
hard-coded. -/
theorem det_cayleyDerivOnSk (X : Sk n) :
    LinearMap.det (cayleyDerivOnSk X).toLinearMap
      = (-2 : ℝ) ^ Fintype.card (nnIndex n) * ((1 + X.1).det)⁻¹ ^ (n - 1) := by
  have hcoe : (cayleyDerivOnSk X).toLinearMap
      = (-2 : ℝ) • (sandwichOnSkCLM ((1 + X.1)⁻¹)).toLinearMap := rfl
  rw [hcoe, LinearMap.det_smul, det_sandwichOnSkCLM,
      Module.finrank_eq_card_basis (skBasis (n := n)),
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

#print axioms det_cayleyDerivOnSk

end Complete

end IwasawaCoC

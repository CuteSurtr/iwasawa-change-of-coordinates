/-
# IwasawaHaarK.lean

Level 1 (Route B): the Haar measure on `K n = O(n)` in Cayley coordinates.

This file develops the orthogonal-group factor of the Iwasawa integration
formula. The Cayley chart `cayleyToK : Sk n → K n` parameterizes the identity
component `SO(n)` (the locus where `1 + Q` is invertible) by skew-symmetric
matrices. Because `O(n)` is a curved group, flat Lebesgue measure on the chart
is NOT left invariant; the correct left invariant density is the Cayley
Jacobian density `ρK X ∝ |det (1 + X)|^{-(n-1)}`.

B1b' (done) defines that density and PINS its exponent by an honest
determinant computation: the intrinsic derivative of the Cayley chart,
expressed as an endomorphism of the identity tangent space `Sk n`, is
`-2 • sandwichOnSkCLM ((1 + X)⁻¹)`, whose determinant is computed by the
already-proven `det_sandwichOnSkCLM`. The resulting exponent `-(n-1)` is read
off, not hard-coded, and the constant matches the `SO(2)` value `2/(1+a²)`.

B1c' (in progress) builds the candidate left invariant measure
`nuK = map cayleyToK (volSk.withDensity ρK)` on the `SO(n)` component, with
`volSk` the Lebesgue measure on `Sk n` from `skBasis`, together with the
measurability facts (`measurable_rhoK`, `measurable_cayleyToK`) that make `nuK`
a genuine pushforward. The remaining step, left invariance of `nuK` under the
Möbius left translation `X ↦ cayleyInv (k₀ · cayley X)` (and then `nuK = c • haarK`
by Haar uniqueness, B1d), is not yet formalized.
-/

import iwasawa_change_of_coords.IwasawaHaar
import iwasawa_change_of_coords.PolynomialNullSet
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace IwasawaCoC

open Matrix Iwasawa MeasureTheory Module
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

/-- **Absolute Jacobian of the Cayley chart.** Taking absolute values in
`det_cayleyDerivOnSk`: the chart Jacobian is `2 ^ card (nnIndex n)` times the
density `|det (1+X)|^{-(n-1)}`. The positive constant `2 ^ card (nnIndex n)` is
absorbed by Haar uniqueness and does not affect the eventual identification
with `haarK`. -/
lemma abs_det_cayleyDerivOnSk (X : Sk n) :
    |LinearMap.det (cayleyDerivOnSk X).toLinearMap|
      = 2 ^ Fintype.card (nnIndex n) * (|(1 + X.1).det|⁻¹) ^ (n - 1) := by
  rw [det_cayleyDerivOnSk, abs_mul, abs_pow, abs_pow, abs_inv]
  norm_num

/-- **The Cayley Haar density on `Sk n`.** `ρK X = |det (1 + X)|^{-(n-1)}`,
written as the natural power of the inverse. By `abs_det_cayleyDerivOnSk` this
is exactly the absolute Cayley chart Jacobian `|det (cayleyDerivOnSk X)|`
divided by the positive constant `2 ^ card (nnIndex n)`. It is the left
invariant density in Cayley coordinates; flat Lebesgue is NOT invariant for
`n ≥ 2`. -/
noncomputable def rhoK (X : Sk n) : ℝ≥0∞ :=
  ENNReal.ofReal ((|(1 + X.1).det|⁻¹) ^ (n - 1))

/-- `ENNReal.ofReal` of the absolute Cayley Jacobian equals `ρK` scaled by the
constant `2 ^ card (nnIndex n)`. -/
lemma ofReal_abs_det_cayleyDerivOnSk (X : Sk n) :
    ENNReal.ofReal |LinearMap.det (cayleyDerivOnSk X).toLinearMap|
      = (2 : ℝ≥0∞) ^ Fintype.card (nnIndex n) * rhoK X := by
  rw [abs_det_cayleyDerivOnSk, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, rhoK]

/-! ### SO(2) sanity check -/

/-- For `n = 2` the skew space `Sk 2` is one dimensional: `card (nnIndex 2) = 1`. -/
lemma card_nnIndex_two : Fintype.card (nnIndex 2) = 1 := by decide

/-- **SO(2) density check.** For `n = 2` the absolute Cayley Jacobian is
`2 · |det (1 + X)|⁻¹`. With `X = ![![0, a], ![-a, 0]]` one computes
`det (1 + X) = 1 + a²`, recovering the classical `SO(2)` Haar density
`2 / (1 + a²)` in the Cayley parameter `a`. This pins the `n = 2` constant to
`2 = 2 ^ card (nnIndex 2)`. -/
lemma abs_det_cayleyDerivOnSk_two (X : Sk 2) :
    |LinearMap.det (cayleyDerivOnSk X).toLinearMap| = 2 * |(1 + X.1).det|⁻¹ := by
  rw [abs_det_cayleyDerivOnSk, card_nnIndex_two, pow_one, pow_one]

/-! ### Measurability of the density -/

/-- `ρK` is continuous on all of `Sk n`. The only possible discontinuity of
`|det (1 + X)|⁻¹` is at `det (1 + X) = 0`, which never occurs for skew `X`
(`one_add_skew_isUnit`), so the inverse is continuous everywhere. -/
lemma continuous_rhoK : Continuous (rhoK : Sk n → ℝ≥0∞) := by
  unfold rhoK
  refine ENNReal.continuous_ofReal.comp (Continuous.pow ?_ (n - 1))
  refine Continuous.inv₀ ?_ (fun X => abs_ne_zero.mpr (one_add_skew_isUnit X).ne_zero)
  exact ((continuous_const.add continuous_subtype_val).matrix_det).abs

/-- `ρK` is measurable (it is even continuous). -/
lemma measurable_rhoK : Measurable (rhoK : Sk n → ℝ≥0∞) :=
  continuous_rhoK.measurable

/-! ### B1c': the candidate invariant measure `nuK` -/

/-- Lebesgue measure on `Sk n`, defined from the basis `skBasis` as the additive
Haar measure giving the `skBasis`-parallelepiped measure one. (There is no
ambient `volume` on the submodule `Sk n`, so we name the Lebesgue measure
explicitly rather than rely on a `MeasureSpace` instance.) -/
noncomputable def volSk : Measure (Sk n) := (skBasis (n := n)).addHaar

/-- **B1c' object.** The candidate left invariant measure on the `SO(n)`
(`det = +1`) component of `K n`, in Cayley coordinates: the density weighted
Lebesgue measure `volSk.withDensity ρK` pushed forward through the Cayley chart
`cayleyToK`. Left invariance under `SO(n)` (the genuine hard step, via the
Möbius left translation `X ↦ cayleyInv (k₀ · cayley X)`) is not yet proven. -/
noncomputable def nuK : Measure (K n) :=
  Measure.map cayleyToK (volSk.withDensity rhoK)

/-- The Cayley chart `cayleyToK` is continuous (its underlying matrix map is
`continuous_cayley_on_skew`). -/
lemma continuous_cayleyToK : Continuous (cayleyToK : Sk n → K n) := by
  apply Continuous.subtype_mk
  exact continuous_cayley_on_skew

/-- The Cayley chart `cayleyToK` is measurable, so `nuK` is a genuine
pushforward (not the junk value of `Measure.map` on a non measurable map). -/
lemma measurable_cayleyToK : Measurable (cayleyToK : Sk n → K n) :=
  continuous_cayleyToK.measurable

/-- Evaluation of `nuK` on a measurable set, via the change of variables for a
pushforward: `nuK s = (volSk.withDensity ρK) (cayleyToK ⁻¹' s)`. -/
lemma nuK_apply {s : Set (K n)} (hs : MeasurableSet s) :
    nuK s = (volSk.withDensity rhoK) (cayleyToK ⁻¹' s) := by
  rw [nuK, Measure.map_apply measurable_cayleyToK hs]

/-! ### B1c' step 1: the Möbius left translation `Ψ k₀`

Left multiplication by `k₀ ∈ SO(n)`, read in Cayley coordinates, is the Möbius
map `Ψ k₀ X = cayleyInv (k₀ · cayley X)`. It is defined wherever the left
translate `k₀ · cayley X` stays in the Cayley image, i.e. on
`cayleyLeftDom k₀ = {X | 1 + k₀ · cayley X invertible}`. The defining identity
`cayley (Ψ k₀ X) = k₀ · cayley X` makes the Cayley chart intertwine `Ψ k₀` with
left multiplication by `k₀`; this is the geometric heart of the left invariance
of `nuK`. -/

/-- The chart domain for left translation by `k₀`: skew `X` whose left translate
`k₀ · cayley X` is still in the Cayley image (`1 + k₀ · cayley X` invertible). -/
def cayleyLeftDom (k₀ : K n) : Set (Sk n) :=
  {X | IsUnit (1 + k₀.1 * cayley X.1).det}

/-- `k₀ · cayley X` is orthogonal, a product of orthogonal matrices. -/
lemma isOrthogonal_k_mul_cayley (k₀ : K n) (X : Sk n) :
    IsOrthogonal (k₀.1 * cayley X.1) :=
  IsOrthogonal.mul k₀.2 (cayley_isOrthogonal X)

/-- The Möbius left translation `Ψ k₀ X = cayleyInv (k₀ · cayley X)` (matrix
valued; it is skew on `cayleyLeftDom k₀`). -/
noncomputable def cayleyLeftTrans (k₀ : K n) (X : Sk n) : Matrix (Fin n) (Fin n) ℝ :=
  cayleyInv (k₀.1 * cayley X.1)

/-- On the domain, the Möbius translate is skew symmetric. -/
lemma cayleyLeftTrans_isSkew (k₀ : K n) {X : Sk n} (hX : X ∈ cayleyLeftDom k₀) :
    (cayleyLeftTrans k₀ X).transpose = -(cayleyLeftTrans k₀ X) :=
  cayleyInv_isSkew _ (isOrthogonal_k_mul_cayley k₀ X) hX

/-- **Defining identity (geometric heart of left invariance).** On the domain,
the Cayley chart sends the Möbius translate to the left translate:
`cayley (Ψ k₀ X) = k₀ · cayley X`. -/
lemma cayley_cayleyLeftTrans (k₀ : K n) {X : Sk n} (hX : X ∈ cayleyLeftDom k₀) :
    cayley (cayleyLeftTrans k₀ X) = k₀.1 * cayley X.1 :=
  cayley_cayleyInv _ hX

/-- The Möbius translate packaged as an element of `Sk n` (valid on the domain). -/
noncomputable def cayleyLeftTransSk (k₀ : K n) {X : Sk n} (hX : X ∈ cayleyLeftDom k₀) :
    Sk n :=
  ⟨cayleyLeftTrans k₀ X, cayleyLeftTrans_isSkew k₀ hX⟩

/-- **Left translation in chart coordinates.** On the domain,
`cayleyToK (Ψ k₀ X) = k₀ * cayleyToK X` in the group `K n`: the Cayley chart
intertwines the Möbius map `Ψ k₀` with left multiplication by `k₀`. -/
lemma cayleyToK_cayleyLeftTransSk (k₀ : K n) {X : Sk n} (hX : X ∈ cayleyLeftDom k₀) :
    cayleyToK (cayleyLeftTransSk k₀ hX) = k₀ * cayleyToK X := by
  apply Subtype.ext
  rw [K_coe_mul]
  show cayley (cayleyLeftTrans k₀ X) = k₀.1 * cayley X.1
  exact cayley_cayleyLeftTrans k₀ hX

/-- `X ↦ k₀ · cayley X` is continuous everywhere on `Sk n`. -/
lemma continuous_k_mul_cayley (k₀ : K n) :
    Continuous (fun X : Sk n => k₀.1 * cayley X.1) :=
  continuous_const.matrix_mul continuous_cayley_on_skew

/-- The chart domain `cayleyLeftDom k₀` is open: it is the preimage of the open
set `{u | u ≠ 0}` under the continuous map `X ↦ det (1 + k₀ · cayley X)`. -/
lemma isOpen_cayleyLeftDom (k₀ : K n) : IsOpen (cayleyLeftDom k₀) := by
  have hcont : Continuous (fun X : Sk n => (1 + k₀.1 * cayley X.1).det) :=
    (continuous_const.add (continuous_k_mul_cayley k₀)).matrix_det
  have hset : cayleyLeftDom k₀
      = (fun X : Sk n => (1 + k₀.1 * cayley X.1).det) ⁻¹' {u | u ≠ 0} := by
    ext X
    simp only [cayleyLeftDom, Set.mem_setOf_eq, Set.mem_preimage, isUnit_iff_ne_zero]
  rw [hset]
  exact hcont.isOpen_preimage _ isOpen_ne

/-- The Möbius left translation `Ψ k₀` is continuous on its domain. The only
discontinuity of the matrix inverse `(1 + k₀ · cayley X)⁻¹` is where
`1 + k₀ · cayley X` is singular, which is exactly off `cayleyLeftDom k₀`. -/
lemma continuousOn_cayleyLeftTrans (k₀ : K n) :
    ContinuousOn (cayleyLeftTrans k₀) (cayleyLeftDom k₀) := by
  intro X hX
  refine ContinuousAt.continuousWithinAt ?_
  have hsub : ContinuousAt (fun Y : Sk n => 1 - k₀.1 * cayley Y.1) X :=
    (continuous_const.sub (continuous_k_mul_cayley k₀)).continuousAt
  have hadd : ContinuousAt (fun Y : Sk n => 1 + k₀.1 * cayley Y.1) X :=
    (continuous_const.add (continuous_k_mul_cayley k₀)).continuousAt
  have hUnitDet : IsUnit ((1 + k₀.1 * cayley X.1).det) := hX
  have hRingInv : ContinuousAt Ring.inverse ((1 + k₀.1 * cayley X.1).det) :=
    NormedRing.inverse_continuousAt hUnitDet.unit
  have hMatInv : ContinuousAt (fun Y : Sk n => (1 + k₀.1 * cayley Y.1)⁻¹) X :=
    ContinuousAt.comp (g := Inv.inv) (f := fun Y : Sk n => 1 + k₀.1 * cayley Y.1)
      (continuousAt_matrix_inv (1 + k₀.1 * cayley X.1) hRingInv) hadd
  show ContinuousAt (fun Y : Sk n => cayleyInv (k₀.1 * cayley Y.1)) X
  unfold cayleyInv
  exact hsub.mul hMatInv

/-! ### B1c' step 1 (continued): the Fréchet derivative of `Ψ k₀`

The Mobius left translation `Ψ k₀ X = cayleyInv (k₀ · cayley X)` is the chain
`cayleyInv ∘ (k₀ · _) ∘ cayley ∘ (·).1`. Each factor is differentiable on the
domain (`cayleyInv` and `cayley` are the SAME formula, so both reuse
`hasFDerivAt_cayley_matrix`), so the chain rule gives the ambient Fréchet
derivative as an explicit continuous linear map. -/

/-- **Ambient Fréchet derivative of `Ψ k₀`.** At a domain point `X`, the matrix
valued Mobius translation has Fréchet derivative the composite of the three chart
derivatives (with left multiplication by `k₀` in the middle). -/
lemma hasFDerivAt_cayleyLeftTrans (k₀ : K n) {X : Sk n} (hX : X ∈ cayleyLeftDom k₀) :
    HasFDerivAt (fun Y : Sk n => cayleyLeftTrans k₀ Y)
      ((cayleyFDerivCLM (k₀.1 * cayley X.1)).comp
        ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) k₀.1).comp
          ((cayleyFDerivCLM X.1).comp (Sk n).subtypeL))) X := by
  have h1 : HasFDerivAt (fun Y : Sk n => (Y : Matrix (Fin n) (Fin n) ℝ))
      (Sk n).subtypeL X := (Sk n).subtypeL.hasFDerivAt
  have h2 : HasFDerivAt cayley (cayleyFDerivCLM X.1) X.1 :=
    hasFDerivAt_cayley_matrix X.1 (one_add_skew_isUnit X)
  have h3 : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℝ => k₀.1 * M)
      (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) k₀.1) (cayley X.1) :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) k₀.1).hasFDerivAt
  have h4 : HasFDerivAt cayleyInv (cayleyFDerivCLM (k₀.1 * cayley X.1)) (k₀.1 * cayley X.1) :=
    hasFDerivAt_cayley_matrix (k₀.1 * cayley X.1) hX
  exact h4.comp X (h3.comp X (h2.comp X h1))

/-- `Ψ k₀` is differentiable on its domain (a regularity ingredient for the change
of variables in step 3). -/
lemma differentiableOn_cayleyLeftTrans (k₀ : K n) :
    DifferentiableOn ℝ (fun Y : Sk n => cayleyLeftTrans k₀ Y) (cayleyLeftDom k₀) :=
  fun X hX => (hasFDerivAt_cayleyLeftTrans k₀ hX).differentiableAt.differentiableWithinAt

#print axioms hasFDerivAt_cayleyLeftTrans
#print axioms differentiableOn_cayleyLeftTrans

/-! ### B1c' step 2 (partial): clearing the Cayley denominator

The chart domain condition `1 + k₀ · cayley X` invertible becomes, after clearing
the `(1 + X)⁻¹` hidden in `cayley X`, the non-vanishing of `det ((1 + X) + k₀ ·
(1 - X))`, which is a polynomial in the entries of `X` (the matrix is affine in
`X`). This is the reduction that turns the chart miss set into the zero set of a
polynomial. The two remaining step 2 facts (that this polynomial is not
identically zero, and that a nonzero polynomial has Lebesgue null zero set) are
NOT formalized here; the latter has no ready Mathlib lemma (see RouteAssessment). -/

/-- Clearing the Cayley denominator:
`(1 + k₀ · cayley X) · (1 + X) = (1 + X) + k₀ · (1 - X)`. -/
lemma one_add_k_cayley_mul (k₀ : K n) (X : Sk n) :
    (1 + k₀.1 * cayley X.1) * (1 + X.1) = (1 + X.1) + k₀.1 * (1 - X.1) := by
  have h : cayley X.1 * (1 + X.1) = 1 - X.1 := by
    unfold cayley
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (one_add_skew_isUnit X), Matrix.mul_one]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, h]

/-- Determinant form of the reduction:
`det (1 + k₀ · cayley X) · det (1 + X) = det ((1 + X) + k₀ · (1 - X))`. -/
lemma det_one_add_k_cayley (k₀ : K n) (X : Sk n) :
    (1 + k₀.1 * cayley X.1).det * (1 + X.1).det
      = ((1 + X.1) + k₀.1 * (1 - X.1)).det := by
  rw [← Matrix.det_mul, one_add_k_cayley_mul]

/-- **Step 2 reduction.** The chart domain is the non-vanishing locus of the
polynomial `det ((1 + X) + k₀ · (1 - X))`: since `det (1 + X) ≠ 0` for skew `X`,
`X ∈ cayleyLeftDom k₀ ↔ det ((1 + X) + k₀ · (1 - X)) ≠ 0`. -/
lemma mem_cayleyLeftDom_iff (k₀ : K n) (X : Sk n) :
    X ∈ cayleyLeftDom k₀ ↔ ((1 + X.1) + k₀.1 * (1 - X.1)).det ≠ 0 := by
  have hb : (1 + X.1).det ≠ 0 := (one_add_skew_isUnit X).ne_zero
  rw [cayleyLeftDom, Set.mem_setOf_eq, isUnit_iff_ne_zero, ← det_one_add_k_cayley,
      mul_ne_zero_iff]
  exact ⟨fun h => ⟨h, hb⟩, fun h => h.1⟩

/-! ### B1c' step 2 (PHASE 2): the chart-miss set `(cayleyLeftDom k₀)ᶜ` is `volSk`-null

By `mem_cayleyLeftDom_iff`, `(cayleyLeftDom k₀)ᶜ = {X | det ((1+X) + k₀ (1-X)) = 0}`,
the zero set of the polynomial `X ↦ det ((1+X) + k₀ (1-X))` in the `skBasis`
coordinates. We transport this set through the linear coordinate equivalence
`skBasis.equivFun` (reindexed to `Fin (card (nnIndex n))`) to `Fin d → ℝ`, exhibit
it as the zero set of an explicit `MvPolynomial`, and invoke
`MvPolynomial.volume_setOf_eval_eq_zero` — provided the polynomial is not
identically zero, i.e. the domain is nonempty. -/

/-- The coordinate equivalence `Sk n ≃L[ℝ] (Fin (card (nnIndex n)) → ℝ)` obtained by
reindexing `skBasis` along `Fintype.equivFin` and taking `equivFunL`. It identifies
`volSk` with the Lebesgue `volume` on `Fin (card (nnIndex n)) → ℝ`
(`map_skCoordEquiv_volSk`). -/
noncomputable def skCoordEquiv :
    Sk n ≃L[ℝ] (Fin (Fintype.card (nnIndex n)) → ℝ) :=
  (skBasis.reindex (Fintype.equivFin (nnIndex n))).equivFunL

/-- `(Pi.basisFun ℝ ι).addHaar` is the Pi–Lebesgue `volume` on `ι → ℝ`. -/
private lemma basisFun_addHaar_eq_volume (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [Basis.addHaar_def, Basis.parallelepiped_basisFun]
  exact addHaarMeasure_eq_volume_pi ι

/-- **Coordinate transport.** The coordinate equivalence pushes `volSk` forward to
the Lebesgue `volume` on `Fin (card (nnIndex n)) → ℝ`. (`volSk` is the additive Haar
of `skBasis`, which reindexing does not change, and `equivFunL` carries that basis to
the standard basis whose `addHaar` is `volume`.) -/
lemma map_skCoordEquiv_volSk :
    Measure.map (skCoordEquiv (n := n)) volSk = volume := by
  set σ := Fintype.equivFin (nnIndex n)
  set b' : Basis (Fin (Fintype.card (nnIndex n))) ℝ (Sk n) := skBasis.reindex σ with hb'
  have hvol : volSk (n := n) = b'.addHaar := by
    rw [volSk, hb', Basis.addHaar_reindex]
  rw [skCoordEquiv, ← hb', hvol, Basis.map_addHaar b' b'.equivFunL]
  have hbasis : b'.map b'.equivFunL.toLinearEquiv = Pi.basisFun ℝ (Fin (Fintype.card (nnIndex n))) := by
    apply Basis.eq_of_apply_eq
    intro i
    funext j
    rw [Basis.map_apply]
    show b'.equivFun (b' i) j = _
    rw [Basis.equivFun_apply, Basis.repr_self, Finsupp.single_apply, Pi.basisFun_apply,
        Pi.single_apply]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [hbasis, basisFun_addHaar_eq_volume]

/-- The polynomial (in the `skBasis` coordinates `Fin (card (nnIndex n)) → ℝ`)
representing the `(l, m)` entry of a generic skew matrix `skOfUpper`: the variable
`X_{(l,m)}` above the diagonal, its negative below, and `0` on the diagonal. -/
noncomputable def skEntryPoly (l m : Fin n) :
    MvPolynomial (Fin (Fintype.card (nnIndex n))) ℝ :=
  if hlm : l < m then MvPolynomial.X (Fintype.equivFin (nnIndex n) ⟨(l, m), hlm⟩)
  else if hml : m < l then - MvPolynomial.X (Fintype.equivFin (nnIndex n) ⟨(m, l), hml⟩)
  else 0

/-- Evaluating `skEntryPoly l m` at coordinates `c` recovers the `(l, m)` entry of the
skew matrix `skOfUpper (c ∘ Fintype.equivFin)`. -/
lemma eval_skEntryPoly (c : Fin (Fintype.card (nnIndex n)) → ℝ) (l m : Fin n) :
    MvPolynomial.eval c (skEntryPoly l m)
      = (skOfUpper (fun ij => c (Fintype.equivFin (nnIndex n) ij)) : Matrix (Fin n) (Fin n) ℝ) l m := by
  rw [skEntryPoly]
  rcases lt_trichotomy l m with hlm | heq | hml
  · rw [dif_pos hlm, MvPolynomial.eval_X, skOfUpper_apply_upper _ hlm]
  · subst heq
    rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), map_zero, skOfUpper_apply_diag]
  · rw [dif_neg (not_lt_of_gt hml), dif_pos hml, map_neg, MvPolynomial.eval_X,
        skOfUpper_apply_lower _ hml]

/-- The inverse coordinate map is `skOfUpper` (reindexed): `skCoordEquiv.symm c` is the
skew matrix whose strict-upper entries are read off from `c` through `Fintype.equivFin`. -/
lemma skCoordEquiv_symm_apply (c : Fin (Fintype.card (nnIndex n)) → ℝ) :
    (skCoordEquiv (n := n)).symm c
      = skOfUpper (fun ij => c (Fintype.equivFin (nnIndex n) ij)) := by
  rw [skCoordEquiv, ContinuousLinearEquiv.symm_apply_eq]
  funext i
  show c i = (skBasis.reindex (Fintype.equivFin (nnIndex n))).equivFun
      (skOfUpper (fun ij => c (Fintype.equivFin (nnIndex n) ij))) i
  rw [Basis.equivFun_apply, Basis.repr_reindex_apply, skBasis_repr_apply,
      skOfUpper_apply_upper _ (((Fintype.equivFin (nnIndex n)).symm i).2)]
  have hidx : (⟨(((Fintype.equivFin (nnIndex n)).symm i).1.1,
        ((Fintype.equivFin (nnIndex n)).symm i).1.2),
        ((Fintype.equivFin (nnIndex n)).symm i).2⟩ : nnIndex n)
      = (Fintype.equivFin (nnIndex n)).symm i := Subtype.ext rfl
  simp only [hidx, Equiv.apply_symm_apply]

/-- The generic-skew-matrix polynomial matrix: entry `(l, m)` is `skEntryPoly l m`. -/
noncomputable def skMatPoly :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Fintype.card (nnIndex n))) ℝ) :=
  Matrix.of (fun l m => skEntryPoly l m)

/-- The polynomial whose zero set (in `skBasis` coordinates) is exactly the
chart-miss set: `det ((1 + k₀) + (1 - k₀) · X_generic)`. By `eval_cayleyDomPoly` it
evaluates to `det ((1+X) + k₀ (1-X))`. -/
noncomputable def cayleyDomPoly (k₀ : K n) :
    MvPolynomial (Fin (Fintype.card (nnIndex n))) ℝ :=
  ((1 + k₀.1).map MvPolynomial.C + (1 - k₀.1).map MvPolynomial.C * skMatPoly).det

/-- **The det polynomial evaluates to the chart-miss determinant.** For every
coordinate vector `c`, with `X := skCoordEquiv.symm c`,
`eval c (cayleyDomPoly k₀) = det ((1 + X) + k₀ (1 - X))`. -/
lemma eval_cayleyDomPoly (k₀ : K n) (c : Fin (Fintype.card (nnIndex n)) → ℝ) :
    MvPolynomial.eval c (cayleyDomPoly k₀)
      = ((1 + ((skCoordEquiv (n := n)).symm c : Matrix (Fin n) (Fin n) ℝ))
          + k₀.1 * (1 - ((skCoordEquiv (n := n)).symm c : Matrix (Fin n) (Fin n) ℝ))).det := by
  rw [cayleyDomPoly, RingHom.map_det, skCoordEquiv_symm_apply]
  congr 1
  set Y : Matrix (Fin n) (Fin n) ℝ :=
    (skOfUpper (fun ij => c (Fintype.equivFin (nnIndex n) ij)) : Matrix (Fin n) (Fin n) ℝ) with hY
  have halg : (1 + k₀.1) + (1 - k₀.1) * Y = (1 + Y) + k₀.1 * (1 - Y) := by noncomm_ring
  rw [← halg]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply,
    map_add, map_sum, map_mul, MvPolynomial.eval_C, skMatPoly, Matrix.of_apply, eval_skEntryPoly, hY]

/-- **Coordinate transport for sets.** A measurable `B ⊆ Sk n` has `volSk B` equal to
the Lebesgue measure of its coordinate image. -/
lemma volSk_eq_volume_image {B : Set (Sk n)} (hB : MeasurableSet B) :
    volSk B = volume ((skCoordEquiv (n := n)) '' B) := by
  have hemb : MeasurableEmbedding (skCoordEquiv (n := n)) := by
    have h := (skCoordEquiv (n := n)).toHomeomorph.measurableEmbedding
    rwa [ContinuousLinearEquiv.coe_toHomeomorph] at h
  have himg : MeasurableSet ((skCoordEquiv (n := n)) '' B) := hemb.measurableSet_image.mpr hB
  conv_lhs => rw [← Set.preimage_image_eq B hemb.injective]
  rw [← Measure.map_apply hemb.measurable himg, map_skCoordEquiv_volSk]

/-- **B1c' step 2 (PHASE 2).** If the chart domain `cayleyLeftDom k₀` is nonempty (so the
determinant polynomial is not identically zero), then its complement — the chart-miss set —
is `volSk`-null. This is the measure-theoretic core: the chart-miss set is the zero locus of
the nonzero polynomial `cayleyDomPoly k₀`, transported to `Fin (card (nnIndex n)) → ℝ`, where
`MvPolynomial.volume_setOf_eval_eq_zero` applies.

The nonemptiness hypothesis is necessary: for `k₀` in the `det = -1` component of `O(n)` the
domain is genuinely empty (`cayley X ∈ SO(n)` always, and `1 + (det -1 orthogonal)` is always
singular), and there the conclusion fails. For `k₀ ∈ SO(n)` the domain is nonempty (the Cayley
image is dense), discharging the hypothesis; that density is not yet formalized here. -/
theorem cayleyLeftDom_compl_null (k₀ : K n) (hne : (cayleyLeftDom k₀).Nonempty) :
    volSk (cayleyLeftDom k₀)ᶜ = 0 := by
  have hBset : (cayleyLeftDom k₀)ᶜ
      = {X : Sk n | ((1 + X.1) + k₀.1 * (1 - X.1)).det = 0} := by
    ext X
    simp only [Set.mem_compl_iff, mem_cayleyLeftDom_iff, Set.mem_setOf_eq, not_not]
  have hcont : Continuous fun X : Sk n => ((1 + X.1) + k₀.1 * (1 - X.1)).det :=
    ((continuous_const.add continuous_subtype_val).add
      (continuous_const.matrix_mul (continuous_const.sub continuous_subtype_val))).matrix_det
  have hmeasB : MeasurableSet {X : Sk n | ((1 + X.1) + k₀.1 * (1 - X.1)).det = 0} :=
    (isClosed_eq hcont continuous_const).measurableSet
  rw [hBset, volSk_eq_volume_image hmeasB]
  have hset : (skCoordEquiv (n := n)) '' {X : Sk n | ((1 + X.1) + k₀.1 * (1 - X.1)).det = 0}
      = {c | MvPolynomial.eval c (cayleyDomPoly k₀) = 0} := by
    ext c
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨X, hX, rfl⟩
      rw [eval_cayleyDomPoly, ContinuousLinearEquiv.symm_apply_apply]
      exact hX
    · intro hc
      refine ⟨(skCoordEquiv (n := n)).symm c, ?_, (skCoordEquiv (n := n)).apply_symm_apply c⟩
      rw [← eval_cayleyDomPoly]
      exact hc
  rw [hset]
  obtain ⟨X₀, hX₀⟩ := hne
  have hp : cayleyDomPoly k₀ ≠ 0 := by
    intro h0
    have hne0 : MvPolynomial.eval ((skCoordEquiv (n := n)) X₀) (cayleyDomPoly k₀) ≠ 0 := by
      rw [eval_cayleyDomPoly, ContinuousLinearEquiv.symm_apply_apply]
      exact (mem_cayleyLeftDom_iff k₀ X₀).mp hX₀
    rw [h0, map_zero] at hne0
    exact hne0 rfl
  exact MvPolynomial.volume_setOf_eval_eq_zero (cayleyDomPoly k₀) hp

/-! ### B1d (reduction): Haar uniqueness on the compact group `K n`

`K n = O(n)` is compact (`instCompactSpaceK`), so its Haar measure is unique up to a
positive scalar. Hence the Cayley chart measure `nuK` equals `haarK` up to a scalar
ONCE `nuK` is known to be left invariant, finite on compacts, and inner regular. The
lemma below discharges the uniqueness step from `Mathlib`, isolating the remaining
work to exactly those three instances on `nuK`. The crux among them is
`IsMulLeftInvariant nuK`, which needs the change of variables for the Mobius left
translation `cayleyLeftTrans` (its density transformation and the null chart miss set
via `MvPolynomial.volume_setOf_eval_eq_zero`); see RouteAssessment. -/

/-- **B1d, reduction to invariance + regularity.** Given that the Cayley chart measure
`nuK` is left invariant, finite on compacts, and inner regular, Haar uniqueness on the
compact group `K n` identifies it with `haarK` up to the positive scalar
`haarScalarFactor nuK haarK`. -/
theorem nuK_eq_smul_haarK_of_invariant
    [IsFiniteMeasureOnCompacts (nuK (n := n))] [Measure.IsMulLeftInvariant (nuK (n := n))]
    [Measure.InnerRegular (nuK (n := n))] :
    (nuK (n := n)) = Measure.haarScalarFactor (nuK (n := n)) (haarK (n := n)) • (haarK (n := n)) :=
  Measure.isMulLeftInvariant_eq_smul_of_innerRegular (nuK (n := n)) (haarK (n := n))

#print axioms nuK_eq_smul_haarK_of_invariant
#print axioms volSk
#print axioms nuK
#print axioms measurable_cayleyToK
#print axioms nuK_apply
#print axioms cayley_cayleyLeftTrans
#print axioms cayleyToK_cayleyLeftTransSk
#print axioms isOpen_cayleyLeftDom
#print axioms continuousOn_cayleyLeftTrans
#print axioms one_add_k_cayley_mul
#print axioms det_one_add_k_cayley
#print axioms mem_cayleyLeftDom_iff
#print axioms continuous_rhoK
#print axioms measurable_rhoK
#print axioms abs_det_cayleyDerivOnSk
#print axioms rhoK
#print axioms ofReal_abs_det_cayleyDerivOnSk
#print axioms abs_det_cayleyDerivOnSk_two

end Complete

end IwasawaCoC

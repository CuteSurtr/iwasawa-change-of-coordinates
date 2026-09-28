/-
mfderiv computations at the identity for the Iwasawa decomposition.

Tier 1, Stage T1-3 (Theorems 1 and 3). Provides:

* **Theorem 1** `cartanInvolution_mfderiv_one_eq_neg_transpose` — the
  differential of the Cartan involution `θ(g) = (gᵀ)⁻¹` at the identity
  is `-transpose`, i.e., `X ↦ -Xᵀ` as a continuous linear map on
  `Matrix _ _ ℝ`. Proved via the chain rule: `d(transpose) = transpose`
  (linear, own derivative), `d(Ring.inverse) at 1 = -id` (from
  `hasFDerivAt_ringInverse`), composition gives `-transpose`.

* **Theorem 3** `iwasawaMap_mfderiv_at_one_eq_lieEquiv` — the
  differential of `iwasawaMap : K × A × UU → G` at `(1, 1, 1)` in the
  current Cayley/log/affine charts. The formula is
  `(X, v, Z) ↦ -2 • X.1 + Matrix.diagonal v + Z.1`; the `-2` comes
  from the project Cayley convention. The theorem name is retained for
  compatibility with existing downstream references, but the statement
  should be read as the scaled chart differential, not the unscaled
  algebraic `iwasawaLieEquiv`.

Theorem 3 lives here rather than next to `iwasawaLieEquiv` in
`IwasawaCoC.lean` because it needs the `IsManifold` instance on `K n`,
which is only finished in `IwasawaSmoothK.lean`.
-/

import iwasawa_change_of_coords.IwasawaSmoothK
import iwasawa_change_of_coords.IwasawaDiffeomorph
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace IwasawaCoC

open Matrix Iwasawa Set Function
open scoped Manifold ContDiff RightActions

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

section MFDerivAtOne

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Continuous-linear lifts of `transpose` and `-transpose` -/

/-- Transpose as a linear map (used to build the continuous-linear version). -/
private def transposeLM :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' := Matrix.transpose_smul

/-- The transpose map as a `ContinuousLinearMap` on `Matrix (Fin n) (Fin n) ℝ`. -/
noncomputable def transposeCLM :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap transposeLM

@[simp] lemma transposeCLM_apply (M : Matrix (Fin n) (Fin n) ℝ) :
    transposeCLM M = M.transpose := rfl

/-- The `-transpose` continuous linear map. -/
noncomputable def negTransposeCLM :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  -transposeCLM

@[simp] lemma negTransposeCLM_apply (M : Matrix (Fin n) (Fin n) ℝ) :
    negTransposeCLM M = -M.transpose := by
  show (-transposeCLM : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) M = -M.transpose
  rw [ContinuousLinearMap.neg_apply, transposeCLM_apply]

/-! ## Theorem 1: `mfderiv (cartanInvolution) 1 = -transpose`

The chain rule applied to `g ↦ (gᵀ)⁻¹ = Ring.inverse ∘ transpose`:
- `d(transpose)` is `transpose` itself (linear maps are their own
  derivatives).
- `d(Ring.inverse) at 1 = -id` (specialization of
  `hasFDerivAt_ringInverse` at the unit `1`, where
  `-mulLeftRight 1 1 1 = -id`).
- Composition: `(-id) ∘ transpose = -transpose`. -/

/-- The ambient extension of `cartanInvolution` on all of `Matrix _ _ ℝ`,
`M ↦ Ring.inverse (Mᵀ)`. Smooth everywhere, equals `(Mᵀ)⁻¹` on
invertible matrices. -/
private noncomputable def cartanInvolutionExt
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Ring.inverse M.transpose

/-- Helper: `(1 : (Matrix _ _ ℝ)ˣ).val = (1 : Matrix _ _ ℝ)`. -/
@[simp] private lemma Units.val_one_matrix :
    ((1 : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) = 1 := rfl

/-- Fréchet derivative of `Ring.inverse` at the identity matrix:
`HasFDerivAt Ring.inverse (-mulLeftRight 1 1) 1`. -/
private theorem hasFDerivAt_ringInverse_one :
    HasFDerivAt (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) 1 1) 1 := by
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := Matrix (Fin n) (Fin n) ℝ)
    (1 : (Matrix (Fin n) (Fin n) ℝ)ˣ)
  -- h : HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑1⁻¹ ↑1⁻¹) ↑1
  -- The coercions ↑1 = 1 and ↑1⁻¹ = 1 simplify by `Units.val_one` and `inv_one`.
  simpa using h

/-- The simplification `-mulLeftRight 1 1 = -id` as a `ContinuousLinearMap`. -/
private lemma neg_mulLeftRight_one_one_eq_neg_id :
    -(ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) 1 1) =
      -ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  ext M
  simp [ContinuousLinearMap.mulLeftRight_apply]

/-- Fréchet derivative of the ambient extension at the identity matrix:
`HasFDerivAt cartanInvolutionExt negTransposeCLM 1`, by chain rule
combining `hasFDerivAt_ringInverse_one` with `transposeCLM.hasFDerivAt`. -/
private theorem hasFDerivAt_cartanInvolutionExt_one :
    HasFDerivAt (cartanInvolutionExt (n := n)) negTransposeCLM 1 := by
  -- cartanInvolutionExt M = Ring.inverse (M.transpose).
  -- Chain rule: HasFDerivAt at 1 of `Ring.inverse ∘ transpose`.
  have h_t : HasFDerivAt (Matrix.transpose : Matrix (Fin n) (Fin n) ℝ → _)
      transposeCLM (1 : Matrix (Fin n) (Fin n) ℝ) :=
    transposeCLM.hasFDerivAt
  -- transpose 1 = 1.
  have h_t_one : (1 : Matrix (Fin n) (Fin n) ℝ).transpose = 1 := Matrix.transpose_one
  have h_inv : HasFDerivAt (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → _)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) 1 1)
      ((1 : Matrix (Fin n) (Fin n) ℝ).transpose) := by
    rw [h_t_one]; exact hasFDerivAt_ringInverse_one
  have h_comp := h_inv.comp 1 h_t
  -- h_comp : HasFDerivAt (Ring.inverse ∘ transpose)
  --              ((-mulLeftRight 1 1).comp transposeCLM) 1
  -- Simplify the derivative: (-mulLeftRight 1 1).comp transposeCLM = negTransposeCLM.
  have h_simp :
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) 1 1).comp transposeCLM =
        negTransposeCLM := by
    ext M
    simp [ContinuousLinearMap.mulLeftRight_apply, transposeCLM_apply, negTransposeCLM_apply]
  rw [h_simp] at h_comp
  -- h_comp : HasFDerivAt (Ring.inverse ∘ transpose) negTransposeCLM 1.
  -- Identify Ring.inverse ∘ transpose with cartanInvolutionExt.
  exact h_comp

/-- Bridge lemma: `Subtype.val ∘ cartanInvolution = cartanInvolutionExt ∘ Subtype.val`
on `G n`. -/
private lemma subtypeVal_comp_cartanInvolution_eq :
    (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘ cartanInvolution =
      cartanInvolutionExt ∘ (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) := by
  funext g
  show (cartanInvolution g).1 = cartanInvolutionExt g.1
  show (g.1.transpose)⁻¹ = Ring.inverse g.1.transpose
  exact Matrix.nonsing_inv_eq_ringInverse g.1.transpose

/-! ### Open-submanifold mfderiv bridge

For `G n` viewed as an open submanifold of `Matrix _ _ ℝ` via the open
embedding `Subtype.val`, the manifold derivative of a function
`f : G n → G n` at a fixed point coincides with the ordinary Fréchet
derivative of an ambient extension. We establish this for our specific
use (`f = cartanInvolution`, `g₀ = ⟨1, _⟩`, extension = `cartanInvolutionExt`)
and for the analogous Theorem 3 use below. The reusable mechanism: derive
`MDifferentiableAt` from `HasFDerivAt` of the extension via the
chart-coord characterization, then identify `mfderiv` through the chain
rule with `mfderiv_extChartAt_self` for the chart map. -/

/-- `Subtype.val : G n → Matrix _ _ ℝ` is `MDifferentiableAt` everywhere,
since it is the singleton-chart map of the open-embedding `ChartedSpace`. -/
lemma mdifferentiableAt_subtypeVal_G (g₀ : G n) :
    MDifferentiableAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) g₀ := by
  -- Subtype.val on G n is exactly the chart map of singletonChartedSpace.
  exact (mdifferentiable_chart g₀).mdifferentiableAt
    (mem_chart_source _ _)

/-- mfderiv of `Subtype.val` at any `g₀ : G n` is the identity CLM. -/
lemma mfderiv_subtypeVal_G (g₀ : G n) :
    mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) g₀ =
    ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  -- Subtype.val on G n equals the chart at g₀ as a function;
  -- mfderiv_extChartAt_self gives the result for the chart.
  have h : (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) =
      extChartAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) g₀ := rfl
  rw [h]
  exact mfderiv_extChartAt_self

/-- `cartanInvolutionExt` is `MDifferentiableAt` at `1` (from
`hasFDerivAt_cartanInvolutionExt_one` plus the model-space conversion). -/
private lemma mdifferentiableAt_cartanInvolutionExt_one :
    MDifferentiableAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (cartanInvolutionExt (n := n)) 1 :=
  hasFDerivAt_cartanInvolutionExt_one.differentiableAt.mdifferentiableAt

/-- ContinuousAt of `cartanInvolution` at the identity. Derived from
ContinuousAt of the matrix extension via the open-embedding property
of `Subtype.val : G n → Matrix _ _ ℝ`. -/
private lemma continuousAt_cartanInvolution_one :
    ContinuousAt (cartanInvolution (n := n)) ⟨1, by simp⟩ := by
  -- The composition `Subtype.val ∘ cartanInvolution` is continuous at
  -- `⟨1, _⟩` (it equals `cartanInvolutionExt ∘ Subtype.val`, a
  -- composition of continuous maps).
  have h_comp : ContinuousAt
      ((Subtype.val : G n → Matrix _ _ ℝ) ∘ cartanInvolution (n := n))
      (⟨1, by simp⟩ : G n) := by
    rw [subtypeVal_comp_cartanInvolution_eq]
    exact ContinuousAt.comp hasFDerivAt_cartanInvolutionExt_one.continuousAt
      continuous_subtype_val.continuousAt
  -- Subtype.val for G n is the singleton chart, an open embedding,
  -- hence a topological embedding. For a topological embedding `j`,
  -- continuity of `j ∘ f` at `x` implies continuity of `f` at `x`.
  exact G_isOpenEmbedding.isEmbedding.continuousAt_iff.mpr h_comp

/-- `cartanInvolution` is `MDifferentiableAt ⟨1, _⟩`: pull back through
the function equality `Subtype.val ∘ cartanInvolution =
cartanInvolutionExt ∘ Subtype.val` plus the open-embedding chart
structure of `G n`. -/
private lemma mdifferentiableAt_cartanInvolution_one :
    MDifferentiableAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (cartanInvolution (n := n)) ⟨1, by simp⟩ := by
  -- The target chart at `cartanInvolution ⟨1, _⟩ = ⟨1, _⟩` is the
  -- singleton chart with `source = univ`, so any point is in source.
  have h_target_chart : cartanInvolution (⟨1, by simp⟩ : G n) ∈
      (chartAt (Matrix (Fin n) (Fin n) ℝ) (⟨1, by simp⟩ : G n)).source := by
    show cartanInvolution _ ∈ Set.univ
    trivial
  rw [mdifferentiableAt_iff_target_of_mem_source h_target_chart]
  refine ⟨continuousAt_cartanInvolution_one, ?_⟩
  -- MDifferentiableAt (extChartAt _ y ∘ cartanInvolution) ⟨1, _⟩
  -- where y = cartanInvolution ⟨1, _⟩. extChartAt _ y as a function
  -- equals Subtype.val for our singletonChartedSpace, so the goal is
  -- MDifferentiableAt (Subtype.val ∘ cartanInvolution) ⟨1, _⟩.
  -- By subtypeVal_comp_cartanInvolution_eq this equals
  -- MDifferentiableAt (cartanInvolutionExt ∘ Subtype.val) ⟨1, _⟩.
  show MDifferentiableAt _ _
      ((Subtype.val : G n → Matrix _ _ ℝ) ∘ cartanInvolution (n := n))
      ⟨1, by simp⟩
  rw [subtypeVal_comp_cartanInvolution_eq]
  exact MDifferentiableAt.comp _ mdifferentiableAt_cartanInvolutionExt_one
    (mdifferentiableAt_subtypeVal_G _)

theorem cartanInvolution_mfderiv_one_eq_neg_transpose :
    mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        (cartanInvolution (n := n)) ⟨1, by simp⟩ = negTransposeCLM := by
  -- Strategy: chain rule on `Subtype.val ∘ cartanInvolution =
  -- cartanInvolutionExt ∘ Subtype.val`. Both sides have known mfderiv
  -- expansions via the chain rule. Equating them, `mfderiv cartanInvolution`
  -- is forced to equal `negTransposeCLM`.
  -- Abbreviations to keep the proof readable.
  set g₀ : G n := ⟨1, by simp⟩ with hg₀
  set I_M : ModelWithCorners ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ) :=
    𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) with hI
  -- Expand `mfderiv (Subtype.val ∘ cartanInvolution) g₀` via the chain rule.
  have h_lhs : mfderiv I_M I_M ((Subtype.val : G n → _) ∘ cartanInvolution) g₀ =
      mfderiv I_M I_M cartanInvolution g₀ := by
    rw [mfderiv_comp g₀ (mdifferentiableAt_subtypeVal_G _) mdifferentiableAt_cartanInvolution_one,
        mfderiv_subtypeVal_G]
    exact ContinuousLinearMap.id_comp _
  -- Expand `mfderiv (cartanInvolutionExt ∘ Subtype.val) g₀` via the chain rule.
  have h_rhs : mfderiv I_M I_M (cartanInvolutionExt ∘ (Subtype.val : G n → _)) g₀ =
      negTransposeCLM := by
    have h_compose := mfderiv_comp g₀
      (f := (Subtype.val : G n → Matrix _ _ ℝ)) (g := cartanInvolutionExt)
      (mdifferentiableAt_cartanInvolutionExt_one) (mdifferentiableAt_subtypeVal_G _)
    rw [h_compose, mfderiv_subtypeVal_G]
    -- Goal: (mfderiv cartanInvolutionExt ↑g₀).comp id = negTransposeCLM.
    -- Substitute mfderiv cartanInvolutionExt at the matrix-level point.
    have h_inner : mfderiv I_M I_M cartanInvolutionExt g₀.1 = negTransposeCLM := by
      rw [mfderiv_eq_fderiv]
      exact hasFDerivAt_cartanInvolutionExt_one.fderiv
    rw [h_inner]
    exact ContinuousLinearMap.comp_id _
  -- The two compositions are equal as functions.
  have h_eq : mfderiv I_M I_M ((Subtype.val : G n → _) ∘ cartanInvolution) g₀ =
      mfderiv I_M I_M (cartanInvolutionExt ∘ (Subtype.val : G n → _)) g₀ := by
    congr 1
    exact subtypeVal_comp_cartanInvolution_eq
  -- Combine.
  rw [h_lhs, h_rhs] at h_eq
  exact h_eq

/-! ## Theorem 3: `mfderiv iwasawaMap (1, 1, 1) = iwasawaLieMap` (with Cayley factor)

**Cayley convention check.** The Cayley transform satisfies
`d(cayley)|_0 = -2 · id` on `Matrix _ _ ℝ` (by the product rule applied
to `(1 - X)(1 + X)⁻¹`: at `X = 0`, `d((1−X)) = -id` and
`d((1+X)⁻¹) = -id` (from `hasFDerivAt_ringInverse` at the unit `1`),
giving `-id + -id = -2·id`). Hence the K-factor's chart-coord
differential at `1 ∈ K n` carries a factor of `-2`: the chart
`cayleyOpenChartAt 1` sends `1 ↦ 0`, and its symm has matrix
derivative `-2·id` at the origin.

So the K-component of the mfderiv contributes `-2·X.1`, not `X.1`.

The chain rule applied to `(k, a, u) ↦ k.val * a.val * u.val`:
- Each component projection is the chart-differential of the
  corresponding subtype embedding (`Subtype.val : K n → Matrix` carries
  the `-2` factor, the others are identity).
- Multiplication `(·) * (·)` has Leibniz differential at `(a, b)` given
  by `(X, Y) ↦ X * b + a * Y`.
- At the identity, `a = b = 1`, so the differential simplifies to
  `(X, Y) ↦ X + Y`.
- Applied twice, the differential at `(1, 1, 1)` of `k * a * u` is
  `(X, H, Y) ↦ X + H + Y` in chart-coord values, but X comes from K
  with the `-2` factor.
- The tangent-space identifications for `T₁(K) ≃ Sk n` (via the Cayley
  chart, scaled by `-2`), `T₁(A) ≃ Fin n → ℝ` (via the log chart, with
  `d(exp)(0) = id` so no factor), `T₁(UU) ≃ NN n` (affine chart, no
  factor) connect this to a scaled `iwasawaLieMap`. -/

/-! ### Theorem 3 sub-formulas

The Theorem 3 proof reduces to the chain rule on
`Subtype.val_G ∘ iwasawaMap = matrix_triple_product ∘ (Subtype.val_K, Subtype.val_A, Subtype.val_UU)`,
the same pattern as Theorem 1. The four sub-formulas below compute the
mfderiv of each component at the identity. -/

/-- Locally re-establish that `cayley = (1 - X) * Ring.inverse (1 + X)`
(the `IwasawaSmoothK` version is `private` to that file). -/
private lemma cayley_eq_ringInverse' :
    (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) =
      fun X => (1 - X) * Ring.inverse (1 + X) := by
  funext X
  show (1 - X) * (1 + X)⁻¹ = (1 - X) * Ring.inverse (1 + X)
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- Pointwise CLM equation: the derivative from the product rule for
`cayley` at 0 equals `-2 • id`. Factored out for clarity. -/
private lemma cayley_deriv_zero_eq :
    ((1 - (0 : Matrix (Fin n) (Fin n) ℝ)) •
        (-ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ)) +
      (-ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ)) <•
        Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 : Matrix (Fin n) (Fin n) ℝ))) =
      -(2 : ℝ) • ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  rw [sub_zero, add_zero, Ring.inverse_one]
  refine ContinuousLinearMap.ext fun M => ?_
  -- Goal at M: (1 • (-id) + (-id) <• 1) M = (-2 • id) M.
  -- The CLM application unfolds via simp; pointwise gives -M + -M = -2 • M.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_smul',
             Pi.smul_apply, ContinuousLinearMap.smul_apply,
             MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
             one_mul, mul_one, smul_eq_mul]
  -- Pointwise goal should now be matrix equation. Use module / ring.
  module

/-- Sub-formula 0: `HasFDerivAt cayley (-2 • id) 0`.

The product rule gives `cayley` a derivative at 0 with one factor each
from `-id` (linearity of `1 - ·`) and `-id` (Ring.inverse chain rule).
Sum: `-2 • id`. -/
theorem hasFDerivAt_cayley_zero :
    HasFDerivAt (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      (-(2 : ℝ) • ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ)) 0 := by
  rw [cayley_eq_ringInverse']
  set MId : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ) with hMId_def
  -- (1 - X) at 0 via `HasFDerivAt.const_sub` applied to `hasFDerivAt_id`.
  have h_id : HasFDerivAt (id : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      MId (0 : Matrix (Fin n) (Fin n) ℝ) := hasFDerivAt_id _
  have h_a : HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℝ => 1 - X) (-MId)
      (0 : Matrix (Fin n) (Fin n) ℝ) :=
    h_id.const_sub (1 : Matrix (Fin n) (Fin n) ℝ)
  -- (1 + X) at 0 via `HasFDerivAt.const_add`.
  have h_one_plus : HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℝ => 1 + X) MId
      (0 : Matrix (Fin n) (Fin n) ℝ) :=
    h_id.const_add (1 : Matrix (Fin n) (Fin n) ℝ)
  -- Ring.inverse (1 + X) at 0: chain rule with derivative -id.
  have h_b : HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℝ => Ring.inverse (1 + X)) (-MId)
      (0 : Matrix (Fin n) (Fin n) ℝ) := by
    have h_inv_at_1 : HasFDerivAt (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → _) (-MId) 1 := by
      have := hasFDerivAt_ringInverse_one (n := n)
      have h_simp : (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) 1 1) = -MId := by
        ext M; simp [hMId_def, ContinuousLinearMap.mulLeftRight_apply]
      rw [h_simp] at this
      exact this
    have h_one_eq : (1 : Matrix (Fin n) (Fin n) ℝ) =
        (fun X : Matrix (Fin n) (Fin n) ℝ => 1 + X) 0 := by
      show (1 : Matrix _ _ ℝ) = 1 + (0 : Matrix _ _ ℝ); rw [add_zero]
    rw [h_one_eq] at h_inv_at_1
    have h_comp := h_inv_at_1.comp (0 : Matrix (Fin n) (Fin n) ℝ) h_one_plus
    have h_comp_eq : ((-MId).comp MId : Matrix (Fin n) (Fin n) ℝ →L[ℝ] _) = -MId := by
      ext M; simp [hMId_def]
    rw [h_comp_eq] at h_comp
    exact h_comp
  -- Apply mul'. The resulting derivative is `(1 - 0) • -MId + -MId <• Ring.inverse (1 + 0)`.
  have h_mul := h_a.mul' h_b
  -- Rewrite to `-(2 : ℝ) • MId` using the helper lemma.
  rwa [cayley_deriv_zero_eq (n := n)] at h_mul

/-! ### Sub-formula 3: `mfderiv (Subtype.val : UU n → Matrix _ _ ℝ) ⟨1, _⟩`

The UU chart is the affine `U ↦ U − 1`; its inverse `Z ↦ Z + 1` has
matrix-level derivative `Z ↦ Z.1` (= `NN.subtypeL` as a CLM). -/

/-- The composition `Subtype.val ∘ chart.symm : NN n → Matrix _ _ ℝ`
unfolds to `Z ↦ Z.1 + 1`. -/
private lemma subtypeVal_UU_comp_chart_symm_apply (Z : NN n) :
    (Subtype.val : UU n → Matrix _ _ ℝ)
      (((@chartAt (NN n) _ (UU n) _ _ ⟨1, IsUpperUnipotent.one⟩).symm : NN n → UU n) Z) =
    Z.1 + 1 := rfl

/-- `Subtype.val ∘ chart.symm : NN n → Matrix _ _ ℝ` has Fréchet derivative
`(NN n).subtypeL` at every point. -/
private lemma hasFDerivAt_subtypeVal_UU_comp_chart_symm (Z : NN n) :
    HasFDerivAt
      (fun Z' : NN n => ((Subtype.val : UU n → Matrix _ _ ℝ)
        (((@chartAt (NN n) _ (UU n) _ _ ⟨1, IsUpperUnipotent.one⟩).symm : NN n → UU n) Z')))
      (NN n).subtypeL Z := by
  -- The function equals `Z' ↦ Z'.1 + 1 = (NN n).subtypeL Z' + 1`.
  -- Linear + const, derivative = (NN n).subtypeL.
  have h_lin : HasFDerivAt ((NN n).subtypeL : NN n → Matrix _ _ ℝ) (NN n).subtypeL Z :=
    (NN n).subtypeL.hasFDerivAt
  exact h_lin.add_const 1

/-- mfderiv of UU's chart map at `⟨1, _⟩` is the identity CLM. -/
private lemma mfderiv_chartAt_UU_one :
    mfderiv (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, (NN n : Type _)))
      (chartAt (NN n) (⟨1, IsUpperUnipotent.one⟩ : UU n) :
         UU n → NN n)
      ⟨1, IsUpperUnipotent.one⟩ = ContinuousLinearMap.id ℝ (NN n) := by
  -- Identify `chartAt _ ⟨1, _⟩ = ⇑(extChartAt I _)` as a function, then apply
  -- `mfderiv_extChartAt_self`.
  have h_eq : (chartAt (NN n) (⟨1, IsUpperUnipotent.one⟩ : UU n) :
      UU n → NN n) = extChartAt (𝓘(ℝ, (NN n : Type _))) (⟨1, IsUpperUnipotent.one⟩ : UU n) := rfl
  rw [h_eq]
  exact mfderiv_extChartAt_self

/-- MDifferentiableAt of UU's chart map at any point (atlas membership). -/
private lemma mdifferentiableAt_chartAt_UU (U : UU n) :
    MDifferentiableAt (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, (NN n : Type _)))
      (chartAt (NN n) U : UU n → NN n) U :=
  (mdifferentiable_chart U).mdifferentiableAt (mem_chart_source _ _)

/-- The function `Subtype.val ∘ chart_symm : NN n → Matrix _ _ ℝ` at any
point `Z` equals `Z.1 + 1`. -/
private lemma subtypeVal_UU_comp_chart_symm_eq :
    ((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) (⟨1, IsUpperUnipotent.one⟩ : UU n)).symm : NN n → UU n))
    = fun Z => (Z.1 : Matrix _ _ ℝ) + 1 := by
  funext Z
  rfl

/-- `Subtype.val ∘ chart_symm : NN n → Matrix _ _ ℝ` is MDifferentiableAt anywhere
(both source and target are model spaces; reduces to DifferentiableAt). -/
private lemma mdifferentiableAt_subtypeVal_UU_comp_chart_symm (Z : NN n) :
    MDifferentiableAt (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) (⟨1, IsUpperUnipotent.one⟩ : UU n)).symm : NN n → UU n))
      Z := by
  rw [subtypeVal_UU_comp_chart_symm_eq]
  exact ((NN n).subtypeL.hasFDerivAt.add_const (1 : Matrix _ _ ℝ)).differentiableAt.mdifferentiableAt

private lemma mfderiv_subtypeVal_UU_one :
    mfderiv (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : UU n → Matrix (Fin n) (Fin n) ℝ)
      ⟨1, IsUpperUnipotent.one⟩ = (NN n).subtypeL := by
  -- Set U₀ := ⟨1, IsUpperUnipotent.one⟩, and work via function equality
  -- `Subtype.val = (Subtype.val ∘ chart_symm) ∘ chart`.
  set U₀ : UU n := ⟨1, IsUpperUnipotent.one⟩
  -- chart U₀ = ⟨0, _⟩.
  have h_chart_eq : (chartAt (NN n) U₀ : UU n → NN n) U₀ =
      (⟨0, (NN n).zero_mem⟩ : NN n) := by
    apply Subtype.ext
    show (1 : Matrix _ _ ℝ) - 1 = 0
    rw [sub_self]
  -- Function equality: Subtype.val = (Subtype.val ∘ chart_symm) ∘ chart.
  have h_fun_eq : (Subtype.val : UU n → Matrix _ _ ℝ) =
      ((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) U₀).symm : NN n → UU n)) ∘
      (chartAt (NN n) U₀ : UU n → NN n) := by
    funext U
    show U.1 = ((chartAt (NN n) U₀).symm (chartAt (NN n) U₀ U)).1
    rw [(chartAt (NN n) U₀).left_inv (by trivial)]
  -- LHS expand via mfderiv_comp.
  have h_chain := mfderiv_comp U₀
    (mdifferentiableAt_subtypeVal_UU_comp_chart_symm (chartAt (NN n) U₀ U₀))
    (mdifferentiableAt_chartAt_UU U₀)
  -- After rewriting, LHS = (chain rule expansion).
  rw [show mfderiv (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : UU n → Matrix (Fin n) (Fin n) ℝ) U₀ =
    mfderiv (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) U₀).symm : NN n → UU n)) ∘
       (chartAt (NN n) U₀ : UU n → NN n)) U₀ from by rw [← h_fun_eq]]
  rw [h_chain, mfderiv_chartAt_UU_one]
  -- Goal: (mfderiv (Subtype.val ∘ chart_symm) (chart U₀)).comp id = NN.subtypeL.
  -- Precompute the LHS factor.
  have h_inner : mfderiv (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) U₀).symm : NN n → UU n))
      ((chartAt (NN n) U₀ : UU n → NN n) U₀) = (NN n).subtypeL := by
    rw [h_chart_eq]
    rw [subtypeVal_UU_comp_chart_symm_eq]
    rw [mfderiv_eq_fderiv]
    exact ((NN n).subtypeL.hasFDerivAt.add_const (1 : Matrix _ _ ℝ)).fderiv
  rw [h_inner]
  exact ContinuousLinearMap.comp_id _

/-! ### Sub-formula 2: `mfderiv (Subtype.val : A n → Matrix _ _ ℝ) ⟨1, _⟩` -/

/-- `Matrix.diagonal` as a continuous linear map. -/
private noncomputable def diagonalCLM :
    (Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ)

@[simp] private lemma diagonalCLM_apply (v : Fin n → ℝ) :
    diagonalCLM v = Matrix.diagonal v := rfl

/-- mfderiv of A's chart map at `⟨1, _⟩` is the identity CLM. -/
private lemma mfderiv_chartAt_A_one :
    mfderiv (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, (Fin n → ℝ)))
      (chartAt (Fin n → ℝ) (⟨1, IsPositiveDiagonal.one⟩ : A n) :
         A n → (Fin n → ℝ))
      ⟨1, IsPositiveDiagonal.one⟩ = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  have h_eq : (chartAt (Fin n → ℝ) (⟨1, IsPositiveDiagonal.one⟩ : A n) :
      A n → Fin n → ℝ) =
      extChartAt (𝓘(ℝ, (Fin n → ℝ))) (⟨1, IsPositiveDiagonal.one⟩ : A n) := rfl
  rw [h_eq]
  exact mfderiv_extChartAt_self

/-- MDifferentiableAt of A's chart map at any point. -/
private lemma mdifferentiableAt_chartAt_A (D : A n) :
    MDifferentiableAt (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, (Fin n → ℝ)))
      (chartAt (Fin n → ℝ) D : A n → Fin n → ℝ) D :=
  (mdifferentiable_chart D).mdifferentiableAt (mem_chart_source _ _)

/-- The composition `Subtype.val ∘ chart_symm : (Fin n → ℝ) → Matrix _ _ ℝ`
unfolds to `v ↦ Matrix.diagonal (Real.exp ∘ v)`. -/
private lemma subtypeVal_A_comp_chart_symm_eq :
    ((Subtype.val : A n → Matrix _ _ ℝ) ∘
      ((chartAt (Fin n → ℝ) (⟨1, IsPositiveDiagonal.one⟩ : A n)).symm :
        (Fin n → ℝ) → A n)) =
    fun v => Matrix.diagonal (fun i => Real.exp (v i)) := by
  funext v
  rfl

/-- Fréchet derivative of `v ↦ Matrix.diagonal (Real.exp ∘ v)` at `v = 0`
equals `diagonalCLM`. Chain rule: inner componentwise exp has derivative
`id` at 0 (`Real.exp '(0) = 1`); outer `Matrix.diagonal` is linear with
derivative `diagonalCLM`. The point match `Pi.exp 0 = fun i => 1` is
fine since `diagonalCLM` (being linear) has the same derivative at every
point. -/
private lemma hasFDerivAt_diag_exp_zero :
    HasFDerivAt (fun v : Fin n → ℝ => Matrix.diagonal (fun i => Real.exp (v i)))
      (diagonalCLM (n := n)) 0 := by
  -- inner: componentwise exp at 0 has fderiv = id.
  have h_exp_pi : HasFDerivAt (fun v : Fin n → ℝ => fun i => Real.exp (v i))
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 := by
    rw [hasFDerivAt_pi']
    intro i
    -- Goal: HasFDerivAt (fun v => Real.exp (v i)) ((proj i).comp id) 0
    have h_exp : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
    have h_fderiv : HasFDerivAt Real.exp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) 1) 0 :=
      h_exp.hasFDerivAt
    have h_proj : HasFDerivAt (fun v : Fin n → ℝ => v i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) 0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
    have h_comp := h_fderiv.comp 0 h_proj
    convert h_comp using 1
    ext v
    simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  -- outer: Matrix.diagonal is linear, derivative = diagonalCLM at any point.
  have h_diag : HasFDerivAt
      (fun w : Fin n → ℝ => Matrix.diagonal w) (diagonalCLM (n := n))
      ((fun v : Fin n → ℝ => fun i => Real.exp (v i)) 0) :=
    diagonalCLM.hasFDerivAt
  have h_comp := h_diag.comp 0 h_exp_pi
  -- h_comp : HasFDerivAt (Matrix.diagonal ∘ Pi.exp) (diagonalCLM ∘ id) 0
  -- Need to simplify diagonalCLM ∘ id = diagonalCLM and identify the function.
  have h_simp : (diagonalCLM (n := n)).comp (ContinuousLinearMap.id ℝ (Fin n → ℝ)) =
      diagonalCLM (n := n) := ContinuousLinearMap.comp_id _
  rw [h_simp] at h_comp
  exact h_comp

private lemma mfderiv_subtypeVal_A_one :
    mfderiv (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : A n → Matrix (Fin n) (Fin n) ℝ)
      ⟨1, IsPositiveDiagonal.one⟩ = diagonalCLM := by
  set D₀ : A n := ⟨1, IsPositiveDiagonal.one⟩
  have h_chart_eq : (chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) D₀ =
      (0 : Fin n → ℝ) := by
    funext i
    show Real.log ((1 : Matrix (Fin n) (Fin n) ℝ) i i) = 0
    rw [Matrix.one_apply_eq, Real.log_one]
  have h_fun_eq : (Subtype.val : A n → Matrix _ _ ℝ) =
      ((Subtype.val : A n → Matrix _ _ ℝ) ∘
        ((chartAt (Fin n → ℝ) D₀).symm : (Fin n → ℝ) → A n)) ∘
      (chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) := by
    funext D
    show D.1 = ((chartAt (Fin n → ℝ) D₀).symm (chartAt (Fin n → ℝ) D₀ D)).1
    rw [(chartAt (Fin n → ℝ) D₀).left_inv (by trivial)]
  have h_mdiff_outer : MDifferentiableAt (𝓘(ℝ, (Fin n → ℝ)))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : A n → Matrix _ _ ℝ) ∘
        ((chartAt (Fin n → ℝ) D₀).symm : (Fin n → ℝ) → A n))
      ((chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) D₀) := by
    rw [h_chart_eq, subtypeVal_A_comp_chart_symm_eq]
    exact hasFDerivAt_diag_exp_zero.differentiableAt.mdifferentiableAt
  have h_chain := mfderiv_comp D₀ h_mdiff_outer (mdifferentiableAt_chartAt_A D₀)
  rw [show mfderiv (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : A n → Matrix (Fin n) (Fin n) ℝ) D₀ =
    mfderiv (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (((Subtype.val : A n → Matrix _ _ ℝ) ∘
        ((chartAt (Fin n → ℝ) D₀).symm : (Fin n → ℝ) → A n)) ∘
       (chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ)) D₀ from by rw [← h_fun_eq]]
  rw [h_chain, mfderiv_chartAt_A_one]
  have h_inner : mfderiv (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : A n → Matrix _ _ ℝ) ∘
        ((chartAt (Fin n → ℝ) D₀).symm : (Fin n → ℝ) → A n))
      ((chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) D₀) = diagonalCLM := by
    rw [h_chart_eq, subtypeVal_A_comp_chart_symm_eq, mfderiv_eq_fderiv]
    exact hasFDerivAt_diag_exp_zero.fderiv
  rw [h_inner]
  exact ContinuousLinearMap.comp_id _

/-! ### Sub-formula 4: matrix triple Leibniz at `(1, 1, 1)` -/

/-- The target derivative CLM for the matrix triple product at `(1, 1, 1)`:
`(X, H, Y) ↦ X + H + Y`. -/
noncomputable def tripleSumCLM :
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
      →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (ContinuousLinearMap.fst ℝ _ _) +
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) +
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] lemma tripleSumCLM_apply (p : Matrix (Fin n) (Fin n) ℝ ×
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :
    tripleSumCLM p = p.1 + p.2.1 + p.2.2 := rfl

lemma hasFDerivAt_triple_mul_at_one :
    HasFDerivAt (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => p.1 * p.2.1 * p.2.2)
      tripleSumCLM (1, 1, 1) := by
  set M₁ : Type _ := Matrix (Fin n) (Fin n) ℝ
  have h_fst : HasFDerivAt (fun p : M₁ × M₁ × M₁ => p.1)
      (ContinuousLinearMap.fst ℝ M₁ (M₁ × M₁)) ((1, 1, 1) : M₁ × M₁ × M₁) :=
    (ContinuousLinearMap.fst ℝ M₁ (M₁ × M₁)).hasFDerivAt
  have h_snd_fst : HasFDerivAt (fun p : M₁ × M₁ × M₁ => p.2.1)
      ((ContinuousLinearMap.fst ℝ M₁ M₁).comp (ContinuousLinearMap.snd ℝ M₁ (M₁ × M₁)))
      ((1, 1, 1) : M₁ × M₁ × M₁) :=
    ((ContinuousLinearMap.fst ℝ M₁ M₁).comp (ContinuousLinearMap.snd ℝ M₁ (M₁ × M₁))).hasFDerivAt
  have h_snd_snd : HasFDerivAt (fun p : M₁ × M₁ × M₁ => p.2.2)
      ((ContinuousLinearMap.snd ℝ M₁ M₁).comp (ContinuousLinearMap.snd ℝ M₁ (M₁ × M₁)))
      ((1, 1, 1) : M₁ × M₁ × M₁) :=
    ((ContinuousLinearMap.snd ℝ M₁ M₁).comp (ContinuousLinearMap.snd ℝ M₁ (M₁ × M₁))).hasFDerivAt
  have h_inner := h_fst.mul' h_snd_fst
  have h_full := h_inner.mul' h_snd_snd
  have h_deriv_eq :
      ((1 : M₁) • ((ContinuousLinearMap.snd ℝ M₁ M₁).comp
          (ContinuousLinearMap.snd ℝ M₁ (M₁ × M₁))) +
        ((1 : M₁) • ((ContinuousLinearMap.fst ℝ M₁ M₁).comp
            (ContinuousLinearMap.snd ℝ M₁ (M₁ × M₁))) +
          (ContinuousLinearMap.fst ℝ M₁ (M₁ × M₁) : M₁ × M₁ × M₁ →L[ℝ] M₁) <•
            (1 : M₁)) <• (1 : M₁)) = tripleSumCLM (n := n) := by
    refine ContinuousLinearMap.ext fun p => ?_
    show (1 : M₁) * (p.2.2 : M₁) + ((1 : M₁) * p.2.1 + p.1 * (1 : M₁)) * (1 : M₁) =
         p.1 + p.2.1 + p.2.2
    simp only [one_mul, mul_one]
    abel
  rw [← h_deriv_eq]
  (convert h_full using 2; simp [Pi.mul_apply])

/-! ### Sub-formula 1: `mfderiv (Subtype.val : K n → Matrix _ _ ℝ) ⟨1, _⟩` -/

/-- mfderiv of K's chart map at `⟨1, _⟩` is the identity CLM. -/
private lemma mfderiv_chartAt_K_one :
    mfderiv (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _)))
      (chartAt (Sk n) (⟨1, IsOrthogonal.one⟩ : K n) : K n → Sk n)
      ⟨1, IsOrthogonal.one⟩ = ContinuousLinearMap.id ℝ (Sk n) := by
  have h_eq : (chartAt (Sk n) (⟨1, IsOrthogonal.one⟩ : K n) : K n → Sk n) =
      extChartAt (𝓘(ℝ, (Sk n : Type _))) (⟨1, IsOrthogonal.one⟩ : K n) := rfl
  rw [h_eq]
  exact mfderiv_extChartAt_self

private lemma mdifferentiableAt_chartAt_K (Q : K n) :
    MDifferentiableAt (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _)))
      (chartAt (Sk n) Q : K n → Sk n) Q :=
  (mdifferentiable_chart Q).mdifferentiableAt (mem_chart_source _ _)

/-- The composition `Subtype.val ∘ chart_symm : Sk n → Matrix _ _ ℝ` at `Q₀ = ⟨1, _⟩`
unfolds to `X ↦ cayley X.1`. -/
private lemma subtypeVal_K_comp_chart_symm_eq :
    ((Subtype.val : K n → Matrix _ _ ℝ) ∘
      ((chartAt (Sk n) (⟨1, IsOrthogonal.one⟩ : K n)).symm : Sk n → K n)) =
    fun X => cayley X.1 := by
  funext X
  show (((chartAt (Sk n) (⟨1, IsOrthogonal.one⟩ : K n)).symm X : K n)).1 = cayley X.1
  rw [show (((chartAt (Sk n) (⟨1, IsOrthogonal.one⟩ : K n)).symm X : K n)).1 =
        cayley X.1 * (1 : Matrix _ _ ℝ) from cayleyOpenChartAt_symm_apply_val
        ⟨1, IsOrthogonal.one⟩ X]
  rw [mul_one]

/-- `Subtype.val ∘ chart_symm : Sk n → Matrix _ _ ℝ` is HasFDerivAt at `0 ∈ Sk n`
with derivative `-(2 : ℝ) • Sk.subtypeL`. Combines `hasFDerivAt_cayley_zero`
with `Sk.subtypeL` linearity. -/
private lemma hasFDerivAt_subtypeVal_K_comp_chart_symm_zero :
    HasFDerivAt
      ((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) (⟨1, IsOrthogonal.one⟩ : K n)).symm : Sk n → K n))
      (-(2 : ℝ) • (Sk n).subtypeL) (0 : Sk n) := by
  rw [subtypeVal_K_comp_chart_symm_eq]
  -- Goal: HasFDerivAt (fun X => cayley X.1) (-(2 : ℝ) • (Sk n).subtypeL) 0
  have h_subtypeL : HasFDerivAt
      ((Sk n).subtypeL : Sk n → Matrix _ _ ℝ) (Sk n).subtypeL (0 : Sk n) :=
    (Sk n).subtypeL.hasFDerivAt
  have h_cay := hasFDerivAt_cayley_zero (n := n)
  -- cayley (subtypeL 0) = cayley 0. The point match: subtypeL 0 = (0 : Matrix _ _ ℝ) = (0 : Sk n).val.
  have h_match : (0 : Matrix (Fin n) (Fin n) ℝ) = ((Sk n).subtypeL (0 : Sk n)) := by simp
  rw [h_match] at h_cay
  have h_comp := h_cay.comp 0 h_subtypeL
  -- h_comp : HasFDerivAt (cayley ∘ subtypeL) ((-(2:ℝ) • id).comp subtypeL) 0
  -- Simplify (-(2:ℝ) • id).comp subtypeL = -(2:ℝ) • subtypeL.
  have h_simp : (-(2 : ℝ) • ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ)).comp
                  (Sk n).subtypeL = -(2 : ℝ) • (Sk n).subtypeL := by
    refine ContinuousLinearMap.ext fun X => ?_
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [h_simp] at h_comp
  exact h_comp

private lemma mfderiv_subtypeVal_K_one :
    mfderiv (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : K n → Matrix (Fin n) (Fin n) ℝ)
      ⟨1, IsOrthogonal.one⟩ = -(2 : ℝ) • (Sk n).subtypeL := by
  set Q₀ : K n := ⟨1, IsOrthogonal.one⟩
  have h_source_mem : Q₀ ∈ (chartAt (Sk n) Q₀).source :=
    mem_chart_source _ _
  have h_source_open : IsOpen (chartAt (Sk n) Q₀).source := (chartAt _ _).open_source
  -- Function equality holds on the chart source (not globally).
  have h_eq_on : Set.EqOn (Subtype.val : K n → Matrix _ _ ℝ)
      (((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n)) ∘
       (chartAt (Sk n) Q₀ : K n → Sk n))
      (chartAt (Sk n) Q₀).source := by
    intro Q hQ
    show Q.1 = ((chartAt (Sk n) Q₀).symm (chartAt (Sk n) Q₀ Q)).1
    rw [(chartAt (Sk n) Q₀).left_inv hQ]
  -- EventuallyEq from EqOn on an open set containing Q₀.
  have h_eq : (Subtype.val : K n → Matrix _ _ ℝ) =ᶠ[nhds Q₀]
      ((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n)) ∘
       (chartAt (Sk n) Q₀ : K n → Sk n) :=
    Filter.eventuallyEq_of_mem (h_source_open.mem_nhds h_source_mem) h_eq_on
  rw [h_eq.mfderiv_eq]
  -- Now chart-coord computation: chart Q₀ = ⟨0, _⟩.
  have h_chart_eq : (chartAt (Sk n) Q₀ : K n → Sk n) Q₀ = (0 : Sk n) := by
    apply Subtype.ext
    show ((cayleyOpenChartAt Q₀) Q₀).1 = 0
    rw [cayleyOpenChartAt_apply_val h_source_mem]
    show cayleyInv (Q₀.1 * Q₀.1.transpose) = 0
    show cayleyInv ((1 : Matrix _ _ ℝ) * (1 : Matrix _ _ ℝ).transpose) = 0
    rw [Matrix.transpose_one, mul_one]
    show (1 - 1 : Matrix _ _ ℝ) * (1 + 1)⁻¹ = 0
    rw [sub_self, zero_mul]
  have h_mdiff_outer : MDifferentiableAt (𝓘(ℝ, (Sk n : Type _)))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n))
      ((chartAt (Sk n) Q₀ : K n → Sk n) Q₀) := by
    rw [h_chart_eq]
    exact hasFDerivAt_subtypeVal_K_comp_chart_symm_zero.differentiableAt.mdifferentiableAt
  rw [mfderiv_comp Q₀ h_mdiff_outer (mdifferentiableAt_chartAt_K Q₀),
      mfderiv_chartAt_K_one]
  have h_inner : mfderiv (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n))
      ((chartAt (Sk n) Q₀ : K n → Sk n) Q₀) = -(2 : ℝ) • (Sk n).subtypeL := by
    rw [h_chart_eq, mfderiv_eq_fderiv]
    exact hasFDerivAt_subtypeVal_K_comp_chart_symm_zero.fderiv
  rw [h_inner]
  exact ContinuousLinearMap.comp_id _

/-! ### Assembly: Theorem 3 -/

/-- MDifferentiableAt for `Subtype.val_K` at the identity. -/
private lemma mdifferentiableAt_subtypeVal_K_one :
    MDifferentiableAt (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : K n → Matrix (Fin n) (Fin n) ℝ)
      ⟨1, IsOrthogonal.one⟩ := by
  set Q₀ : K n := ⟨1, IsOrthogonal.one⟩
  have h_source_mem : Q₀ ∈ (chartAt (Sk n) Q₀).source := mem_chart_source _ _
  have h_source_open : IsOpen (chartAt (Sk n) Q₀).source := (chartAt _ _).open_source
  have h_eq_on : Set.EqOn (Subtype.val : K n → Matrix _ _ ℝ)
      (((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n)) ∘
       (chartAt (Sk n) Q₀ : K n → Sk n))
      (chartAt (Sk n) Q₀).source := by
    intro Q hQ
    show Q.1 = ((chartAt (Sk n) Q₀).symm (chartAt (Sk n) Q₀ Q)).1
    rw [(chartAt (Sk n) Q₀).left_inv hQ]
  have h_eq : (Subtype.val : K n → Matrix _ _ ℝ) =ᶠ[nhds Q₀]
      ((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n)) ∘
       (chartAt (Sk n) Q₀ : K n → Sk n) :=
    Filter.eventuallyEq_of_mem (h_source_open.mem_nhds h_source_mem) h_eq_on
  have h_chart_eq : (chartAt (Sk n) Q₀ : K n → Sk n) Q₀ = (0 : Sk n) := by
    apply Subtype.ext
    show ((cayleyOpenChartAt Q₀) Q₀).1 = 0
    rw [cayleyOpenChartAt_apply_val h_source_mem]
    show cayleyInv (Q₀.1 * Q₀.1.transpose) = 0
    show cayleyInv ((1 : Matrix _ _ ℝ) * (1 : Matrix _ _ ℝ).transpose) = 0
    rw [Matrix.transpose_one, mul_one]
    show (1 - 1 : Matrix _ _ ℝ) * (1 + 1)⁻¹ = 0
    rw [sub_self, zero_mul]
  have h_outer_mdiff : MDifferentiableAt (𝓘(ℝ, (Sk n : Type _)))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : K n → Matrix _ _ ℝ) ∘
        ((chartAt (Sk n) Q₀).symm : Sk n → K n))
      ((chartAt (Sk n) Q₀ : K n → Sk n) Q₀) := by
    rw [h_chart_eq]
    exact hasFDerivAt_subtypeVal_K_comp_chart_symm_zero.differentiableAt.mdifferentiableAt
  have h_mdiff_rhs := h_outer_mdiff.comp Q₀ (mdifferentiableAt_chartAt_K Q₀)
  exact h_mdiff_rhs.congr_of_eventuallyEq h_eq

/-- MDifferentiableAt for `Subtype.val_A` at the identity. -/
private lemma mdifferentiableAt_subtypeVal_A_one :
    MDifferentiableAt (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : A n → Matrix (Fin n) (Fin n) ℝ)
      ⟨1, IsPositiveDiagonal.one⟩ := by
  set D₀ : A n := ⟨1, IsPositiveDiagonal.one⟩
  have h_chart_eq : (chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) D₀ = (0 : Fin n → ℝ) := by
    funext i
    show Real.log ((1 : Matrix (Fin n) (Fin n) ℝ) i i) = 0
    rw [Matrix.one_apply_eq, Real.log_one]
  have h_fun_eq : (Subtype.val : A n → Matrix _ _ ℝ) =
      ((Subtype.val : A n → Matrix _ _ ℝ) ∘
        ((chartAt (Fin n → ℝ) D₀).symm : (Fin n → ℝ) → A n)) ∘
      (chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) := by
    funext D
    show D.1 = ((chartAt (Fin n → ℝ) D₀).symm (chartAt (Fin n → ℝ) D₀ D)).1
    rw [(chartAt (Fin n → ℝ) D₀).left_inv (by trivial)]
  rw [h_fun_eq]
  have h_outer_mdiff : MDifferentiableAt (𝓘(ℝ, (Fin n → ℝ)))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : A n → Matrix _ _ ℝ) ∘
        ((chartAt (Fin n → ℝ) D₀).symm : (Fin n → ℝ) → A n))
      ((chartAt (Fin n → ℝ) D₀ : A n → Fin n → ℝ) D₀) := by
    rw [h_chart_eq, subtypeVal_A_comp_chart_symm_eq]
    exact hasFDerivAt_diag_exp_zero.differentiableAt.mdifferentiableAt
  exact h_outer_mdiff.comp D₀ (mdifferentiableAt_chartAt_A D₀)

/-- MDifferentiableAt for `Subtype.val_UU` at the identity. -/
private lemma mdifferentiableAt_subtypeVal_UU_one :
    MDifferentiableAt (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : UU n → Matrix (Fin n) (Fin n) ℝ)
      ⟨1, IsUpperUnipotent.one⟩ := by
  set U₀ : UU n := ⟨1, IsUpperUnipotent.one⟩
  have h_fun_eq : (Subtype.val : UU n → Matrix _ _ ℝ) =
      ((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) U₀).symm : NN n → UU n)) ∘
      (chartAt (NN n) U₀ : UU n → NN n) := by
    funext U
    show U.1 = ((chartAt (NN n) U₀).symm (chartAt (NN n) U₀ U)).1
    rw [(chartAt (NN n) U₀).left_inv (by trivial)]
  rw [h_fun_eq]
  have h_outer_mdiff : MDifferentiableAt (𝓘(ℝ, (NN n : Type _)))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Subtype.val : UU n → Matrix _ _ ℝ) ∘
        ((chartAt (NN n) U₀).symm : NN n → UU n))
      ((chartAt (NN n) U₀ : UU n → NN n) U₀) :=
    (hasFDerivAt_subtypeVal_UU_comp_chart_symm _).differentiableAt.mdifferentiableAt
  exact h_outer_mdiff.comp U₀ (mdifferentiableAt_chartAt_UU U₀)

theorem iwasawaMap_mfderiv_at_one_eq_lieEquiv :
    ∀ (X : Sk n) (v : Fin n → ℝ) (Z : NN n),
    (mfderiv ((𝓘(ℝ, (Sk n : Type _))).prod
                ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (iwasawaMap : K n × A n × UU n → G n)
              ((⟨1, IsOrthogonal.one⟩, ⟨1, IsPositiveDiagonal.one⟩,
                ⟨1, IsUpperUnipotent.one⟩))) (X, v, Z) =
      (-2 : ℝ) • X.1 + Matrix.diagonal v + Z.1 := by
  intro X v Z
  -- Single-pass assembly using the patterns from the research pass:
  -- 1. Lift sub-formulas 1, 2, 3 to HasMFDerivAt via MDifferentiableAt + mfderiv equality.
  -- 2. Compose with fst/snd projections to get HasMFDerivAt of the product extraction.
  -- 3. Combine via HasMFDerivAt.prodMk into HasMFDerivAt of subtypes_triple.
  -- 4. Compose with hasFDerivAt_triple_mul_at_one.hasMFDerivAt via HasMFDerivAt.comp.
  -- 5. This gives HasMFDerivAt (Subtype.val_G ∘ iwasawaMap) p₀ L.
  -- 6. Strip Subtype.val_G via the fact that it's the chart with mfderiv = id;
  --    use that HasMFDerivAt iwasawaMap p₀ L follows from HasMFDerivAt of the
  --    Subtype.val composition.
  set k₀ : K n := ⟨1, IsOrthogonal.one⟩ with hk₀_def
  set a₀ : A n := ⟨1, IsPositiveDiagonal.one⟩ with ha₀_def
  set u₀ : UU n := ⟨1, IsUpperUnipotent.one⟩ with hu₀_def
  -- Step 1.
  have h_K : HasMFDerivAt (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : K n → Matrix (Fin n) (Fin n) ℝ) k₀
      (-(2 : ℝ) • (Sk n).subtypeL) := by
    have h := (mdifferentiableAt_subtypeVal_K_one (n := n)).hasMFDerivAt
    rw [mfderiv_subtypeVal_K_one] at h
    exact h
  have h_A : HasMFDerivAt (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : A n → Matrix (Fin n) (Fin n) ℝ) a₀ diagonalCLM := by
    have h := (mdifferentiableAt_subtypeVal_A_one (n := n)).hasMFDerivAt
    rw [mfderiv_subtypeVal_A_one] at h
    exact h
  have h_UU : HasMFDerivAt (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Subtype.val : UU n → Matrix (Fin n) (Fin n) ℝ) u₀ ((NN n).subtypeL) := by
    have h := (mdifferentiableAt_subtypeVal_UU_one (n := n)).hasMFDerivAt
    rw [mfderiv_subtypeVal_UU_one] at h
    exact h
  -- Set up the product manifold structure abbreviations.
  set p₀ : K n × A n × UU n := (k₀, a₀, u₀) with hp₀_def
  set I_prod := ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _))))) with hI_prod
  set I_M := (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) with hI_M
  -- Step 2: HasMFDerivAt for product projections.
  have h_fst : HasMFDerivAt I_prod (𝓘(ℝ, (Sk n : Type _)))
      (Prod.fst : K n × A n × UU n → K n) p₀
      (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)) :=
    hasMFDerivAt_fst p₀
  have h_snd : HasMFDerivAt I_prod ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _))))
      (Prod.snd : K n × A n × UU n → A n × UU n) p₀
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)) :=
    hasMFDerivAt_snd p₀
  have h_fst_snd : HasMFDerivAt ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _))))
      (𝓘(ℝ, (Fin n → ℝ)))
      (Prod.fst : A n × UU n → A n) (a₀, u₀)
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)) :=
    hasMFDerivAt_fst (a₀, u₀)
  have h_snd_snd : HasMFDerivAt ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _))))
      (𝓘(ℝ, (NN n : Type _)))
      (Prod.snd : A n × UU n → UU n) (a₀, u₀)
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)) :=
    hasMFDerivAt_snd (a₀, u₀)
  -- Build intermediate compositions for the A and UU branches.
  have h_proj_a : HasMFDerivAt I_prod (𝓘(ℝ, (Fin n → ℝ)))
      (fun p : K n × A n × UU n => p.2.1) p₀
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) :=
    h_fst_snd.comp p₀ h_snd
  have h_proj_u : HasMFDerivAt I_prod (𝓘(ℝ, (NN n : Type _)))
      (fun p : K n × A n × UU n => p.2.2) p₀
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) :=
    h_snd_snd.comp p₀ h_snd
  -- Step 3: Compose each subtype embedding with the projections.
  have h_K_full : HasMFDerivAt I_prod I_M
      (fun p : K n × A n × UU n => p.1.1) p₀
      ((-(2 : ℝ) • (Sk n).subtypeL).comp
        (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))) :=
    h_K.comp p₀ h_fst
  have h_A_full : HasMFDerivAt I_prod I_M
      (fun p : K n × A n × UU n => p.2.1.1) p₀
      (diagonalCLM.comp
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))) :=
    h_A.comp p₀ h_proj_a
  have h_UU_full : HasMFDerivAt I_prod I_M
      (fun p : K n × A n × UU n => p.2.2.1) p₀
      (((NN n).subtypeL).comp
        ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))) :=
    h_UU.comp p₀ h_proj_u
  -- Step 4: Combine via HasMFDerivAt.prodMk.
  have h_triple : HasMFDerivAt I_prod
      (I_M.prod (I_M.prod I_M))
      (fun p : K n × A n × UU n => (p.1.1, p.2.1.1, p.2.2.1)) p₀
      (((-(2 : ℝ) • (Sk n).subtypeL).comp
          (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
        ((diagonalCLM.comp
            ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))).prod
          (((NN n).subtypeL).comp
            ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))))) :=
    h_K_full.prodMk (h_A_full.prodMk h_UU_full)
  -- Step 5: Compose with the matrix triple multiplication HasFDerivAt.
  -- The function `(p1, p2, p3) ↦ p1 * p2 * p3 : Matrix × Matrix × Matrix → Matrix`
  -- at (1, 1, 1) has fderiv = tripleSumCLM. Lift to HasMFDerivAt via
  -- `HasFDerivAt.hasMFDerivAt` (both source and target are model spaces).
  have h_mul : HasMFDerivAt (I_M.prod (I_M.prod I_M)) I_M
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
          Matrix (Fin n) (Fin n) ℝ => p.1 * p.2.1 * p.2.2)
      (1, 1, 1) tripleSumCLM :=
    hasFDerivAt_triple_mul_at_one.hasMFDerivAt
  -- The composition (matrix_triple_mul ∘ subtypes_triple) p₀ = 1 * 1 * 1 = 1
  -- (the basepoint where matrix_triple_mul's derivative lives).
  have h_basepoint : (fun p : K n × A n × UU n => (p.1.1, p.2.1.1, p.2.2.1)) p₀ =
      ((1, 1, 1) : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [← h_basepoint] at h_mul
  have h_full : HasMFDerivAt I_prod I_M
      (fun p : K n × A n × UU n => p.1.1 * p.2.1.1 * p.2.2.1) p₀
      (tripleSumCLM.comp _) := h_mul.comp p₀ h_triple
  -- Step 6: This function equals `(Subtype.val_G ∘ iwasawaMap)` and
  -- additionally agrees with iwasawaMap at the chart-coord level (since
  -- Subtype.val_G IS the chart for G, the chart-coord function for
  -- iwasawaMap is exactly Subtype.val_G ∘ iwasawaMap composed with
  -- the source chart symm). HasMFDerivAt of the matrix-valued composition
  -- coincides definitionally with HasMFDerivAt of iwasawaMap.
  have h_iwasawa : HasMFDerivAt I_prod I_M
      (fun p : K n × A n × UU n =>
        ((iwasawaMap : K n × A n × UU n → G n) p).1) p₀
      (tripleSumCLM.comp _) := h_full
  -- Step 6: Bridge to the G n target via the open-submanifold chart structure.
  -- We establish `MDifferentiableAt iwasawaMap p₀` (G-valued) using the
  -- target-chart characterization (the singleton chart of G n has source = univ),
  -- then apply the chain rule on `Subtype.val ∘ iwasawaMap` with
  -- `mfderiv_subtypeVal_G = id` to derive
  -- `mfderiv (Subtype.val ∘ iwasawaMap) p₀ = mfderiv iwasawaMap p₀`.
  have h_mdiff_iwasawa_G : MDifferentiableAt I_prod I_M
      (iwasawaMap : K n × A n × UU n → G n) p₀ := by
    have h_target_chart : iwasawaMap p₀ ∈
        (chartAt (Matrix (Fin n) (Fin n) ℝ) (iwasawaMap p₀)).source := by
      show iwasawaMap p₀ ∈ Set.univ
      trivial
    rw [mdifferentiableAt_iff_target_of_mem_source h_target_chart]
    refine ⟨?_, ?_⟩
    · -- ContinuousAt iwasawaMap p₀: pull back through the open embedding.
      exact G_isOpenEmbedding.isEmbedding.continuousAt_iff.mpr
        h_iwasawa.continuousAt
    · -- MDifferentiableAt (extChartAt_target ∘ iwasawaMap) p₀.
      -- extChartAt I_M (iwasawaMap p₀) is Subtype.val for the singleton chart.
      exact h_iwasawa.mdifferentiableAt
  -- Compute mfderiv iwasawaMap via the chain rule on Subtype.val ∘ iwasawaMap.
  have h_final : mfderiv I_prod I_M
      (iwasawaMap : K n × A n × UU n → G n) p₀ =
      mfderiv I_prod I_M
        (fun p : K n × A n × UU n =>
          ((iwasawaMap : K n × A n × UU n → G n) p).1) p₀ := by
    have h_chain := mfderiv_comp p₀
      (f := (iwasawaMap : K n × A n × UU n → G n))
      (g := (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ))
      (mdifferentiableAt_subtypeVal_G _) h_mdiff_iwasawa_G
    -- h_chain : mfderiv (Subtype.val ∘ iwasawaMap) p₀ =
    --           (mfderiv Subtype.val (iwasawaMap p₀)).comp (mfderiv iwasawaMap p₀)
    rw [mfderiv_subtypeVal_G] at h_chain
    -- h_chain : mfderiv (Subtype.val ∘ iwasawaMap) p₀ = id.comp (mfderiv iwasawaMap p₀)
    -- Use h_chain.trans (id_comp) to get: mfderiv (Sub ∘ iw) p₀ = mfderiv iw p₀.
    exact (h_chain.trans (ContinuousLinearMap.id_comp _)).symm
  -- Combine: mfderiv iwasawaMap p₀ = L (from h_iwasawa.mfderiv).
  rw [h_final, h_iwasawa.mfderiv]
  -- Goal: (tripleSumCLM.comp _) (X, v, Z) = -2 • X.1 + diagonal v + Z.1.
  -- Unfold the composed CLM application via `rfl`-equal evaluation
  -- (tripleSumCLM_apply, comp_apply, prod_apply are all rfl by definition).
  rfl

end MFDerivAtOne

end IwasawaCoC

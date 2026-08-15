/-
Iwasawa decomposition: smooth manifold structure on the orthogonal group K = O(n).

Tier 1, Stage T1-1. Closes the `IsManifold` gap left open in
`iwasawa_change_of_coords.IwasawaCoC`. The Cayley chart atlas
`{ cayleyOpenChartAt Q | Q : K n }` is already in place there; what is
missing is chart-transition smoothness. We prove the five-piece
decomposition:

* `contDiffAt_cayley`           — Cayley is `C∞` at any matrix `M` with
                                  `1 + M` invertible.
* `contDiffOn_cayley`           — its `ContDiffOn` corollary on the open
                                  set `{M | IsUnit (1 + M).det}`.
* `contDiff_mul_right_const`,
  `contDiff_mul_left_const`     — multiplication by a fixed matrix.
* `cayleyChart_transition_source_eq` — set-equality identifying the
                                  abstract transition source with the
                                  concrete invertibility set.
* `contDiffOn_cayleyChart_transition` — chart-transition smoothness.

The final `instIsManifoldK` is then assembled via Mathlib's
`isManifold_of_contDiffOn`.

Implementation note. The Cayley smoothness route requires a `NormedRing`
structure on `Matrix (Fin n) (Fin n) ℝ`, which we obtain via the
`linfty op` operator-norm choice (`Matrix.linftyOpNormedRing` and
companions). This is topologically equivalent to the `sup of sup` norm
used elsewhere in `IwasawaCoC`, so the resulting `IsManifold` instance
is the same up to defeq of the model space.
-/

import iwasawa_change_of_coords.IwasawaCoC
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Normed

namespace IwasawaCoC

open Matrix Iwasawa Topology Set Function
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ## Local `NormedRing` instances on the matrix algebra

We use the `linfty op` operator norm so that `Matrix (Fin n) (Fin n) ℝ`
becomes a `NormedRing` (hence `HasSummableGeomSeries`), which is the
hypothesis of `contDiffAt_ringInverse`. -/

section MatrixNormedRing

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Lemma 1.1 and 1.2: Cayley is `C∞` where `1 + ·` is invertible -/

/-- `Matrix.inv` and `Ring.inverse` agree pointwise, so the Cayley
transform may be rewritten as `(1 - X) * Ring.inverse (1 + X)`. -/
private lemma cayley_eq_ringInverse :
    (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) =
      fun X => (1 - X) * Ring.inverse (1 + X) := by
  funext X
  show (1 - X) * (1 + X)⁻¹ = (1 - X) * Ring.inverse (1 + X)
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- **Lemma 1.1.** The Cayley transform `X ↦ (1 - X)(1 + X)⁻¹` is `C∞`
at any matrix `M` for which `1 + M` is invertible. -/
theorem contDiffAt_cayley {M : Matrix (Fin n) (Fin n) ℝ}
    (h : IsUnit (1 + M : Matrix (Fin n) (Fin n) ℝ)) :
    ContDiffAt ℝ ⊤ (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) M := by
  rw [cayley_eq_ringInverse]
  refine ContDiffAt.mul ?_ ?_
  · -- `(1 - X)` is `C∞`: constant minus identity.
    exact (contDiff_const.sub contDiff_id).contDiffAt
  · -- `Ring.inverse (1 + X)` at `M`: compose smoothness of `Ring.inverse`
    -- at the unit `1 + M` with smoothness of `X ↦ 1 + X`.
    have h_inv : ContDiffAt ℝ ⊤ Ring.inverse
        ((h.unit : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) :=
      contDiffAt_ringInverse (𝕜 := ℝ) (n := (⊤ : WithTop ℕ∞)) h.unit
    have h_eq : ((h.unit : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) = 1 + M :=
      h.unit_spec
    rw [h_eq] at h_inv
    have h_arg : ContDiffAt ℝ ⊤ (fun X : Matrix (Fin n) (Fin n) ℝ => 1 + X) M :=
      (contDiff_const.add contDiff_id).contDiffAt
    exact h_inv.comp M h_arg

/-- **Lemma 1.2.** The Cayley transform is `C∞` on the open set
`{ M | IsUnit (1 + M).det }`. -/
theorem contDiffOn_cayley :
    ContDiffOn ℝ ⊤ (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      { M : Matrix (Fin n) (Fin n) ℝ | IsUnit ((1 + M).det) } := by
  intro M hM
  have h : IsUnit (1 + M : Matrix (Fin n) (Fin n) ℝ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hM
  exact (contDiffAt_cayley h).contDiffWithinAt

/-! ## Lemma 1.3: multiplication by a fixed matrix is `C∞` -/

/-- Right multiplication by a fixed matrix is `C∞`. -/
theorem contDiff_mul_right_const (R : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun M : Matrix (Fin n) (Fin n) ℝ => M * R) := by
  have h : ContDiff ℝ ⊤ (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      p.1 * p.2) := contDiff_mul
  exact h.comp (contDiff_id.prodMk contDiff_const)

/-- Left multiplication by a fixed matrix is `C∞`. -/
theorem contDiff_mul_left_const (L : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun M : Matrix (Fin n) (Fin n) ℝ => L * M) := by
  have h : ContDiff ℝ ⊤ (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      p.1 * p.2) := contDiff_mul
  exact h.comp (contDiff_const.prodMk contDiff_id)

/-! ## Lemma 1.4: Explicit formula for `(cayleyOpenChartAt Q₀).symm` -/

/-- The inverse of the translated Cayley chart sends `X : Sk n` to the
orthogonal matrix `cayley X · Q₀`. Concretely, the underlying matrix
of `(cayleyOpenChartAt Q₀).symm X` is `cayley X.1 * Q₀.1`. -/
theorem cayleyOpenChartAt_symm_apply_val (Q₀ : K n) (X : Sk n) :
    ((cayleyOpenChartAt Q₀).symm X).1 = cayley X.1 * Q₀.1 := rfl

/-! ## Lemma 1.5: Chart transition source as a concrete invertibility set -/

/-- The source of the chart transition `cayleyOpenChartAt Q₀ ⁻¹ ≫ cayleyOpenChartAt Q₁`
equals the open subset of `Sk n` where the inverse appearing inside
`cayleyInv` is well-defined:
`{ X : Sk n | IsUnit ((1 + (cayley X · Q₀) · Q₁.transpose).det) }`. -/
theorem cayleyChart_transition_source_eq (Q₀ Q₁ : K n) :
    ((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)).source =
      { X : Sk n | IsUnit ((1 + (cayley X.1 * Q₀.1) * Q₁.1.transpose).det) } := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      cayleyOpenChartAt_target]
  ext X
  simp only [Set.univ_inter, Set.mem_preimage, cayleyOpenChartAt_source,
             Set.mem_setOf_eq, cayleyOpenChartAt_symm_apply_val]

/-! ## Lemma 1.6: Explicit formula for the chart-transition

The forward formula of `cayleyOpenChartAt Q₁` cannot be reduced by
`rfl` because the underlying `openPartialHomeomorphSubtypeCoe.symm`
uses `Function.invFun` (noncomputable). We instead use the chart's
`left_inv` property to derive the forward formula on the source. -/

/-- Underlying matrix of `cayleyOpenChartAt Q₁` at any K-element in
its source. -/
theorem cayleyOpenChartAt_apply_val {Q₁ : K n} {Q : K n}
    (hQ : Q ∈ (cayleyOpenChartAt Q₁).source) :
    ((cayleyOpenChartAt Q₁) Q).1 = cayleyInv (Q.1 * Q₁.1.transpose) := by
  -- Set Y := (cayleyOpenChartAt Q₁) Q.
  set Y := (cayleyOpenChartAt Q₁) Q with hY
  -- left_inv: e.symm (e Q) = Q for Q in source.
  have hLI : (cayleyOpenChartAt Q₁).symm Y = Q := (cayleyOpenChartAt Q₁).left_inv hQ
  -- Take .1: ((cayleyOpenChartAt Q₁).symm Y).1 = Q.1.
  have h1 : ((cayleyOpenChartAt Q₁).symm Y).1 = Q.1 := by rw [hLI]
  -- Rewrite the LHS using the symm-apply-val rfl lemma: it equals `cayley Y.1 * Q₁.1`.
  rw [cayleyOpenChartAt_symm_apply_val] at h1
  -- h1 : cayley Y.1 * Q₁.1 = Q.1. Right-multiply by Q₁.1ᵀ and use `Q₁ Q₁ᵀ = 1`.
  have hQ1_orth : Q₁.1 * Q₁.1.transpose = 1 := Q₁.2
  have h2 : cayley Y.1 = Q.1 * Q₁.1.transpose := by
    have hcong := congrArg (· * Q₁.1.transpose) h1
    simp only at hcong
    rw [Matrix.mul_assoc, hQ1_orth, Matrix.mul_one] at hcong
    exact hcong
  -- Apply `cayleyInv` to both sides; the LHS collapses by `cayleyInv_cayley`.
  have h3 := congrArg cayleyInv h2
  rw [cayleyInv_cayley Y] at h3
  exact h3

/-- Underlying matrix of the chart-transition map at any `X : Sk n` in
the source. -/
theorem cayleyChart_transition_apply_val (Q₀ Q₁ : K n) {X : Sk n}
    (hX : X ∈ ((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)).source) :
    (((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)) X).1 =
      cayleyInv ((cayley X.1 * Q₀.1) * Q₁.1.transpose) := by
  -- (e.symm.trans e') X = e' (e.symm X)  -- `trans_apply` is rfl.
  show ((cayleyOpenChartAt Q₁) ((cayleyOpenChartAt Q₀).symm X)).1 = _
  rw [cayleyChart_transition_source_eq] at hX
  -- (cayleyOpenChartAt Q₀).symm X ∈ (cayleyOpenChartAt Q₁).source.
  have hQ_source : (cayleyOpenChartAt Q₀).symm X ∈ (cayleyOpenChartAt Q₁).source := by
    rw [cayleyOpenChartAt_source]
    show IsUnit ((1 + ((cayleyOpenChartAt Q₀).symm X).1 * Q₁.1.transpose).det)
    rw [cayleyOpenChartAt_symm_apply_val]
    exact hX
  rw [cayleyOpenChartAt_apply_val hQ_source, cayleyOpenChartAt_symm_apply_val]

/-! ## Antisymmetric projection: a continuous-linear retract `Matrix → Sk n`

The map `M ↦ (M - Mᵀ)/2` is a `ContinuousLinearMap` that restricts to
the identity on `Sk n`. We use it as a retract so ContDiff of a
matrix-valued function automatically lifts to ContDiff of the
corresponding `Sk n`-valued function. -/

/-- Linear antisymmetric projection `Matrix _ _ ℝ →ₗ[ℝ] Sk n`. -/
private noncomputable def skLinearProj :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Sk n where
  toFun M := ⟨(1/2 : ℝ) • (M - M.transpose), by
    show ((1/2 : ℝ) • (M - M.transpose)).transpose = -((1/2 : ℝ) • (M - M.transpose))
    rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose,
        ← smul_neg, neg_sub]⟩
  map_add' M N := by
    apply Subtype.ext
    show (1/2 : ℝ) • ((M + N) - (M + N).transpose) =
         (1/2 : ℝ) • (M - M.transpose) + (1/2 : ℝ) • (N - N.transpose)
    rw [Matrix.transpose_add]
    simp only [smul_sub, smul_add]
    abel
  map_smul' c M := by
    apply Subtype.ext
    show (1/2 : ℝ) • ((c • M) - (c • M).transpose) =
         c • (1/2 : ℝ) • (M - M.transpose)
    rw [Matrix.transpose_smul, ← smul_sub, smul_comm c (1/2 : ℝ)]

/-- Continuous antisymmetric projection. -/
noncomputable def skProj : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Sk n :=
  LinearMap.toContinuousLinearMap skLinearProj

@[simp] lemma skProj_apply_val (M : Matrix (Fin n) (Fin n) ℝ) :
    (skProj M : Sk n).1 = (1/2 : ℝ) • (M - M.transpose) := rfl

/-- `skProj` is a left inverse of the inclusion `Sk n → Matrix _ _ ℝ`. -/
lemma skProj_subtype_val (X : Sk n) : skProj X.1 = X := by
  apply Subtype.ext
  show (1/2 : ℝ) • (X.1 - X.1.transpose) = X.1
  have hX : X.1.transpose = -X.1 := X.2
  rw [hX, sub_neg_eq_add, show X.1 + X.1 = (2 : ℝ) • X.1 by rw [two_smul], smul_smul]
  norm_num

/-! ## Theorem 1.7: Chart-transition smoothness -/

/-- **Main chart-transition smoothness lemma.** The chart transition map
between any two translated Cayley charts at `Q₀, Q₁ : K n` is `C∞` on
its source. -/
theorem contDiffOn_cayleyChart_transition (Q₀ Q₁ : K n) :
    ContDiffOn ℝ ⊤
      (((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)) : Sk n → Sk n)
      ((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)).source := by
  -- Source set abbreviation.
  set S := ((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)).source with hS_def
  -- Matrix-level transition function.
  let g : Sk n → Matrix (Fin n) (Fin n) ℝ :=
    fun X => cayleyInv ((cayley X.1 * Q₀.1) * Q₁.1.transpose)
  -- Step 1: g is ContDiffOn S.
  have h_g_contdiff : ContDiffOn ℝ ⊤ g S := by
    intro X hX
    -- Translate hX into the explicit invertibility predicate.
    have hX' : IsUnit ((1 + (cayley X.1 * Q₀.1) * Q₁.1.transpose).det) := by
      rw [hS_def, cayleyChart_transition_source_eq] at hX
      exact hX
    apply ContDiffAt.contDiffWithinAt
    -- Build the composition of smooth pieces step by step.
    have h_subtypeL : ContDiff ℝ ⊤
        (fun X : Sk n => (X.1 : Matrix (Fin n) (Fin n) ℝ)) :=
      (Sk n).subtypeL.contDiff
    -- Inner cayley smoothness: 1 + X.1 is always invertible for X skew.
    have h_one_add_inner : IsUnit (1 + X.1 : Matrix (Fin n) (Fin n) ℝ) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (one_add_skew_isUnit X)
    have h_cay : ContDiffAt ℝ ⊤
        (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) X.1 :=
      contDiffAt_cayley h_one_add_inner
    -- Right multiplications by constants.
    have h_mul0 : ContDiff ℝ ⊤ (fun M : Matrix (Fin n) (Fin n) ℝ => M * Q₀.1) :=
      contDiff_mul_right_const Q₀.1
    have h_mul1 : ContDiff ℝ ⊤
        (fun M : Matrix (Fin n) (Fin n) ℝ => M * Q₁.1.transpose) :=
      contDiff_mul_right_const Q₁.1.transpose
    -- Outer cayleyInv = cayley smoothness at the inner expression.
    have h_one_add_outer :
        IsUnit (1 + (cayley X.1 * Q₀.1) * Q₁.1.transpose : Matrix (Fin n) (Fin n) ℝ) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hX'
    have h_cayInv : ContDiffAt ℝ ⊤
        (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
        ((cayley X.1 * Q₀.1) * Q₁.1.transpose) :=
      contDiffAt_cayley h_one_add_outer
    -- Build the inner composition `fun X => (cayley X.1 * Q₀.1) * Q₁.1.transpose`.
    have h_inner_full : ContDiffAt ℝ ⊤
        (fun X : Sk n => (cayley X.1 * Q₀.1) * Q₁.1.transpose) X := by
      refine h_mul1.contDiffAt.comp X ?_
      refine h_mul0.contDiffAt.comp X ?_
      exact h_cay.comp X h_subtypeL.contDiffAt
    -- cayleyInv is cayley (same formula), so cayleyInv expression is the composition.
    have h_target : g X = cayley ((cayley X.1 * Q₀.1) * Q₁.1.transpose) := rfl
    show ContDiffAt ℝ ⊤ g X
    have : g = cayley ∘ (fun X : Sk n => (cayley X.1 * Q₀.1) * Q₁.1.transpose) := rfl
    rw [this]
    exact h_cayInv.comp X h_inner_full
  -- Step 2: chart_transition X = skProj (g X) on S.
  have h_T_eq : ∀ X ∈ S,
      ((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)) X = skProj (g X) := by
    intro X hX
    have h_val : (((cayleyOpenChartAt Q₀).symm.trans (cayleyOpenChartAt Q₁)) X).1 = g X :=
      cayleyChart_transition_apply_val Q₀ Q₁ hX
    -- skProj (g X) = skProj ((chart_transition X).1) = chart_transition X (left inverse).
    rw [← h_val, skProj_subtype_val]
  -- Step 3: skProj ∘ g is ContDiffOn S (composition with CLM); congr to get chart_transition.
  have h_comp : ContDiffOn ℝ ⊤ (fun X : Sk n => skProj (g X)) S :=
    skProj.contDiff.comp_contDiffOn h_g_contdiff
  exact h_comp.congr h_T_eq

/-! ## Final assembly: `IsManifold (𝓘(ℝ, Sk n)) ⊤ (K n)` -/

/-- **Theorem 1.8.** The orthogonal group `K n = O(n)` is a smooth
manifold modeled on the skew-symmetric matrices `Sk n`. -/
instance instIsManifoldK : IsManifold (𝓘(ℝ, (Sk n : Type _))) ⊤ (K n) := by
  refine isManifold_of_contDiffOn (𝓘(ℝ, (Sk n : Type _))) ⊤ (K n) ?_
  rintro e e' ⟨Q₀, rfl⟩ ⟨Q₁, rfl⟩
  -- The model with corners is the identity on `Sk n`, so `I ∘ f ∘ I.symm = f`
  -- and `I.symm ⁻¹' S ∩ range I = S`. Use `mfld_simps` to discharge.
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
             Set.preimage_id, Set.range_id, Set.inter_univ]
  exact contDiffOn_cayleyChart_transition Q₀ Q₁

end MatrixNormedRing

end IwasawaCoC

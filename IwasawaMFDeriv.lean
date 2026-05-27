/- 
General-point mfderiv on `G n` via the direct matrix Leibniz formula.

Tier 1, Stage T1-4. Builds on T1-3's identity-case mfderiv computation
(`iwasawaMap_mfderiv_at_one_eq_lieEquiv` in IwasawaMFDerivAtOne.lean)
to derive the mfderiv at general points in the current
Cayley/log/affine charts.

Important named objects:

* `mfderiv_leftMulG_at`: left multiplication `g ↦ g₀ * g` on `G n` is
  smooth, with mfderiv at any point equal to the linear
  left-multiplication map by `g₀.1`.
* `conjugation_NN_by_diagonal`: the `Ad(a)` action `X ↦ a · X · a⁻¹`
  on `NN n`, with derivative at 1 a linear map. This feeds the
  positive-root density computation.
* `iwasawaMatrixLeibnizCLM`: the actual derivative of `iwasawaMap` in
  the current chart convention.
* `lieTwistCLM`: an auxiliary twist map useful for the root-density
  factor, not the full derivative of `iwasawaMap`.
* `mfderiv_iwasawaMap_at_factored`: the proved general-point derivative
  theorem, with right-hand side `iwasawaMatrixLeibnizCLM k a u`.
-/

import iwasawa_change_of_coords.IwasawaMFDerivAtOne

namespace IwasawaCoC

open Matrix Iwasawa Set Function
open scoped Manifold ContDiff RightActions

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

section MatrixNormedRing

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Lemma 1: left multiplication is smooth with the expected mfderiv

`leftMulG g₀ g = ⟨g₀.1 * g.1, _⟩` is the left-multiplication map on
`G n`. Smoothness follows from the matrix-level CLM smoothness of
`(g₀.1 * ·) : Matrix → Matrix` and the open-submanifold pattern. The
mfderiv at any point equals `ContinuousLinearMap.mul ℝ _ g₀.1` via the
`mfderiv_subtypeVal_G = id` bridge. -/

/-- Left-multiplication map on `G n` by a fixed element `g₀`. The
`G n`-valued result has nonzero determinant because
`det (g₀.1 * g.1) = det g₀.1 * det g.1`, both nonzero. -/
noncomputable def leftMulG (g₀ : G n) : G n → G n := fun g =>
  ⟨g₀.1 * g.1, by
    rw [Matrix.det_mul]
    exact mul_ne_zero g₀.2 g.2⟩

@[simp] lemma leftMulG_apply_val (g₀ g : G n) :
    (leftMulG g₀ g).1 = g₀.1 * g.1 := rfl

/-- The matrix-level left-multiplication by `g₀.1` is `ContMDiff`. -/
private lemma contMDiff_matrix_leftMul (g₀ : G n) :
    ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
              (fun M : Matrix (Fin n) (Fin n) ℝ => g₀.1 * M) := by
  -- (g₀.1 * ·) is the CLM `ContinuousLinearMap.mul ℝ _ g₀.1` applied;
  -- CLMs are smooth.
  exact (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) g₀.1).contMDiff

/-- `Subtype.val ∘ leftMulG g₀ = (g₀.1 * ·) ∘ Subtype.val` definitionally
(both unfold to `fun g : G n => g₀.1 * g.1`). -/
private lemma subtypeVal_leftMulG_eq (g₀ : G n) :
    (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘ leftMulG g₀ =
      (fun M : Matrix (Fin n) (Fin n) ℝ => g₀.1 * M) ∘
        (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) := rfl

/-- **T1-4 smoothness component.** Left multiplication `leftMulG g₀` is
`ContMDiff ⊤` on `G n`. -/
theorem contMDiff_leftMulG (g₀ : G n) :
    ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
              (leftMulG g₀ : G n → G n) := by
  -- Compose `(g₀.1 * ·)` with `Subtype.val`, then use
  -- `ContMDiff.of_comp_isOpenEmbedding` to descend to G n target.
  have h_subval : ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                            (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) :=
    contMDiff_isOpenEmbedding G_isOpenEmbedding
  have h_comp : ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                          (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                          ((fun M : Matrix (Fin n) (Fin n) ℝ => g₀.1 * M) ∘
                            (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) :=
    (contMDiff_matrix_leftMul g₀).comp h_subval
  -- (Subtype.val ∘ leftMulG g₀) = ((g₀.1 * ·) ∘ Subtype.val) by rfl.
  rw [← subtypeVal_leftMulG_eq] at h_comp
  exact ContMDiff.of_comp_isOpenEmbedding G_isOpenEmbedding h_comp

/-- `MDifferentiableAt` corollary of `contMDiff_leftMulG`. -/
private lemma mdifferentiableAt_leftMulG (g₀ g : G n) :
    MDifferentiableAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (leftMulG g₀ : G n → G n) g :=
  ((contMDiff_leftMulG g₀).contMDiffAt).mdifferentiableAt (by decide)

/-- The matrix-level mfderiv of `M ↦ g₀.1 * M` at any point is the
CLM `ContinuousLinearMap.mul ℝ _ g₀.1` itself (CLMs are their own
derivatives). -/
private lemma mfderiv_matrix_leftMul (g₀ : G n) (M : Matrix (Fin n) (Fin n) ℝ) :
    mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (fun N : Matrix (Fin n) (Fin n) ℝ => g₀.1 * N) M =
      ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) g₀.1 := by
  exact (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) g₀.1).mfderiv_eq

private lemma mdifferentiableAt_matrix_leftMul (g₀ : G n) (M : Matrix (Fin n) (Fin n) ℝ) :
    MDifferentiableAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (fun N : Matrix (Fin n) (Fin n) ℝ => g₀.1 * N) M :=
  (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) g₀.1).mdifferentiableAt

/-- `MDifferentiableAt` of the matrix-level `Subtype.val : G n → Matrix`
at any point (re-exposed from `IwasawaMFDerivAtOne`). -/
private lemma mdifferentiableAt_subtypeVal_G' (g : G n) :
    MDifferentiableAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) g :=
  (mdifferentiable_chart g).mdifferentiableAt (mem_chart_source _ _)

private lemma mfderiv_subtypeVal_G' (g : G n) :
    mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) g =
      ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  have h : (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) =
      extChartAt (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) g := rfl
  rw [h]
  exact mfderiv_extChartAt_self

/-- **T1-4 Lemma 1.** Left multiplication by a fixed `g₀ ∈ G n` has
mfderiv at any point `g ∈ G n` equal to the CLM left-multiplication
map `X ↦ g₀.1 * X` (via `ContinuousLinearMap.mul`). -/
theorem mfderiv_leftMulG_at (g₀ g : G n) :
    mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (leftMulG g₀ : G n → G n) g =
      ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) g₀.1 := by
  -- Strategy: chain rule on `Subtype.val ∘ leftMulG g₀ = (g₀.1 * ·) ∘ Subtype.val`.
  -- LHS chain: mfderiv (Subtype.val ∘ leftMulG g₀) g = id.comp (mfderiv leftMulG g) = mfderiv leftMulG g.
  -- RHS chain: mfderiv ((g₀.1 * ·) ∘ Subtype.val) g = (CLM.mul g₀.1).comp id = CLM.mul g₀.1.
  have h_lhs := mfderiv_comp g
    (f := (leftMulG g₀ : G n → G n))
    (g := (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ))
    (mdifferentiableAt_subtypeVal_G' _) (mdifferentiableAt_leftMulG g₀ g)
  -- h_lhs : mfderiv (Subtype.val ∘ leftMulG g₀) g =
  --         (mfderiv Subtype.val (leftMulG g₀ g)).comp (mfderiv (leftMulG g₀) g)
  rw [mfderiv_subtypeVal_G'] at h_lhs
  -- h_lhs : mfderiv (Subtype.val ∘ leftMulG g₀) g = id.comp (mfderiv (leftMulG g₀) g)
  have h_rhs := mfderiv_comp g
    (f := (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ))
    (g := (fun N : Matrix (Fin n) (Fin n) ℝ => g₀.1 * N))
    (mdifferentiableAt_matrix_leftMul g₀ g.1)
    (mdifferentiableAt_subtypeVal_G' g)
  -- h_rhs : mfderiv ((g₀.1 * ·) ∘ Subtype.val) g =
  --         (mfderiv (g₀.1 * ·) g.1).comp (mfderiv Subtype.val g)
  rw [mfderiv_matrix_leftMul, mfderiv_subtypeVal_G'] at h_rhs
  -- h_rhs : mfderiv ((g₀.1 * ·) ∘ Subtype.val) g = (CLM.mul g₀.1).comp id
  -- Simplify h_lhs to drop id.comp (using `.trans` pattern from T1-3).
  have h_lhs' :
      mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        ((Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘ leftMulG g₀) g =
      mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        (leftMulG g₀ : G n → G n) g :=
    h_lhs.trans (ContinuousLinearMap.id_comp _)
  -- Simplify h_rhs to drop comp.id.
  have h_rhs' :
      mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        ((fun N : Matrix (Fin n) (Fin n) ℝ => g₀.1 * N) ∘
          (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) g =
      ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) g₀.1 :=
    h_rhs.trans (ContinuousLinearMap.comp_id _)
  -- The two compositions are definitionally equal, so their mfderivs agree.
  have h_eq_mfderiv :
      mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        ((Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘ leftMulG g₀) g =
      mfderiv (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        ((fun N : Matrix (Fin n) (Fin n) ℝ => g₀.1 * N) ∘
          (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) g := rfl
  -- Chain: mfderiv leftMulG g = mfderiv (Subtype.val ∘ leftMulG) g
  --                            = mfderiv ((g₀.1 * ·) ∘ Subtype.val) g
  --                            = CLM.mul g₀.1.
  exact h_lhs'.symm.trans (h_eq_mfderiv.trans h_rhs')

/-! ## Lemma 2: conjugation by a positive diagonal preserves `NN n`

For `a : A n` (positive diagonal) and `X : NN n` (strictly upper
triangular), the conjugate `a · X · a⁻¹` is again strictly upper
triangular. The (i, j) entry is `(a_i / a_j) · X_{ij}`, in particular
zero when `j ≤ i`. The conjugation is a continuous linear map
`NN n →L[ℝ] NN n`, with explicit eigenvalues on the basis of
elementary strictly upper triangular matrices. -/

/-- For positive diagonal `a`, the matrix inverse `a.1⁻¹` agrees with
the diagonal-style inverse `diagInv a.1`. -/
private lemma A_inv_eq_diagInv (a : A n) :
    a.1⁻¹ = Iwasawa.diagInv a.1 :=
  Matrix.inv_eq_left_inv a.2.diagInv_mul_self

/-- Entry-level formula for conjugation of any matrix `X` by a positive
diagonal `a`: `(a · X · a⁻¹) i j = a_i · X_{ij} · (a_j)⁻¹`. -/
private lemma A_conj_entry (a : A n) (X : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (a.1 * X * a.1⁻¹) i j = a.1 i i * X i j * (a.1 j j)⁻¹ := by
  rw [A_inv_eq_diagInv]
  -- Step 1: outer mul_apply.
  have h1 : (a.1 * X * Iwasawa.diagInv a.1) i j =
      ∑ k, (a.1 * X) i k * Iwasawa.diagInv a.1 k j := Matrix.mul_apply
  -- Step 2: the outer sum reduces to the k = j term (diagInv off-diag = 0).
  have h2 : (∑ k, (a.1 * X) i k * Iwasawa.diagInv a.1 k j) =
      (a.1 * X) i j * Iwasawa.diagInv a.1 j j := by
    rw [Finset.sum_eq_single j]
    · intro k _ hk
      rw [Iwasawa.diagInv_off_diag hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- Step 3: inner mul_apply.
  have h3 : (a.1 * X) i j = ∑ l, a.1 i l * X l j := Matrix.mul_apply
  -- Step 4: the inner sum reduces to the l = i term (a.1 off-diag = 0).
  have h4 : (∑ l, a.1 i l * X l j) = a.1 i i * X i j := by
    rw [Finset.sum_eq_single i]
    · intro l _ hl
      rw [a.2.1 i l (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Chain: rewrite using h1, h2, then h3, h4, then unfold diagInv_diag.
  rw [h1, h2, h3, h4, Iwasawa.diagInv_diag]

/-- For `a : A n` and `X : NN n`, the conjugate `a.1 * X.1 * a.1⁻¹`
is in `NN n` (strictly upper triangular). -/
private lemma adNN_mem (a : A n) (X : NN n) :
    a.1 * X.1 * a.1⁻¹ ∈ NN n := by
  intro i j hji
  rw [A_conj_entry]
  have hX : X.1 i j = 0 := X.2 i j hji
  rw [hX]; ring

/-- **T1-4 Lemma 2.** Conjugation by a positive diagonal matrix
restricts to a continuous linear endomorphism of the strictly
upper-triangular Lie algebra `NN n`. -/
noncomputable def adNN (a : A n) : NN n →L[ℝ] NN n :=
  ((ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) a.1 a.1⁻¹).comp
    (NN n).subtypeL).codRestrict (NN n) (adNN_mem a)

@[simp] lemma adNN_apply_val (a : A n) (X : NN n) :
    (adNN a X : Matrix (Fin n) (Fin n) ℝ) = a.1 * X.1 * a.1⁻¹ := rfl

/-- **Eigenvalue structure.** For `a : A n` and `X : NN n`, the (i, j)
entry of `adNN a X` is `(a.1 i i / a.1 j j) * X.1 i j`. In particular
for `i < j` (the only nonzero positions of `X`), the multiplier is the
positive ratio `a_i / a_j`. -/
theorem adNN_entry (a : A n) (X : NN n) (i j : Fin n) :
    (adNN a X : Matrix (Fin n) (Fin n) ℝ) i j =
      (a.1 i i / a.1 j j) * X.1 i j := by
  rw [adNN_apply_val, A_conj_entry, div_eq_mul_inv]
  ring

/-- The basic statement of T1-4 Lemma 2: conjugation by a positive
diagonal `a` is the linear map `adNN a` on `NN n`, with the diagonal
eigenvalue structure recorded above. -/
theorem conjugation_NN_by_diagonal (a : A n) :
    ∀ (X : NN n) (i j : Fin n),
      (adNN a X : Matrix (Fin n) (Fin n) ℝ) i j =
        (a.1 i i / a.1 j j) * X.1 i j :=
  fun X i j => adNN_entry a X i j

/-! ## Lemma 3: general-point mfderiv of `iwasawaMap`

Smoothness `contMDiff_iwasawaMap` (in `IwasawaDiffeomorph.lean`)
already establishes `ContMDiff` of `iwasawaMap` at every point. From
this we extract `MDifferentiableAt` at any `(k₀, a₀, u₀)`. The full
closed-form mfderiv at a general point combines:

* The matrix-level Leibniz on the triple product
  `(M, N, P) ↦ M * N * P` at `(k₀.1, a₀.1, u₀.1)`, which equals
  `(δM, δN, δP) ↦ δM * a₀.1 * u₀.1 + k₀.1 * δN * u₀.1 + k₀.1 * a₀.1 * δP`.
* The chart-coord differentials of the three subtype embeddings
  `Subtype.val : K n → Matrix`, `Subtype.val : A n → Matrix`,
  `Subtype.val : UU n → Matrix` at the general points `k₀, a₀, u₀`.

The identity-case version is `iwasawaMap_mfderiv_at_one_eq_lieEquiv`
in `IwasawaMFDerivAtOne.lean`. The general-point chart-coord
differentials at K, A, UU at non-identity points are themselves
chain-rule sub-problems (Cayley chart at `Q₀ ≠ 1` for K, log chart at
`a₀ ≠ 1` for A; UU's affine chart is uniform). These are deferred
sub-lemmas for a future closure of the full formula.

The result below records the achievable progress at this stage: the
function is differentiable at every point, and its mfderiv extracted
from the smoothness statement is well-defined. -/

/-- **T1-4 Lemma 3 (partial).** `iwasawaMap` is `MDifferentiableAt`
at every point. The full explicit mfderiv formula at general points
is deferred (it requires chart-coord differentials of K, A, UU at
non-identity points). -/
theorem mdifferentiableAt_iwasawaMap_at (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    MDifferentiableAt ((𝓘(ℝ, (Sk n : Type _))).prod
                        ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                      (iwasawaMap : K n × A n × UU n → G n) (k₀, a₀, u₀) :=
  ((contMDiff_iwasawaMap (n := n)).contMDiffAt).mdifferentiableAt (by decide)

/-- **T1-4 Lemma 3.** `iwasawaMap` has an `mfderiv` at every point
`(k₀, a₀, u₀)` (the manifold differential exists and is a CLM from
`Sk n × ((Fin n → ℝ) × NN n)` into `Matrix (Fin n) (Fin n) ℝ`).
This is a direct consequence of `MDifferentiableAt`. -/
theorem mfderiv_iwasawaMap_at (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    HasMFDerivAt ((𝓘(ℝ, (Sk n : Type _))).prod
                    ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                  (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                  (iwasawaMap : K n × A n × UU n → G n) (k₀, a₀, u₀)
                  (mfderiv _ _ _ (k₀, a₀, u₀)) :=
  (mdifferentiableAt_iwasawaMap_at k₀ a₀ u₀).hasMFDerivAt

/-! ## Lemma 3 explicit CLM forms

The full closed-form mfderiv at the identity (Theorem 3 from
`IwasawaMFDerivAtOne.lean`) is a pointwise equation
`mfderiv iwasawaMap (1,1,1) (X, v, Z) = -2 • X.1 + diag v + Z.1`.
We package the RHS as a single CLM `iwasawaLieMapCLM` and lift the
pointwise equation to a CLM equation `mfderiv iwasawaMap (1,1,1) =
iwasawaLieMapCLM`. This is used downstream by T1-5 (abstract Jacobian)
to take determinants. -/

/-- The Lie algebra differential of `iwasawaMap` at the identity, as a
single CLM `Sk n × ((Fin n → ℝ) × NN n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ`.
Its application is `(X, v, Z) ↦ -2 • X.1 + diag v + Z.1`. Built from
the three component CLMs: `(-2) • Sk.subtypeL`, `diagonalLinearMap`,
and `NN.subtypeL`. -/
noncomputable def iwasawaLieMapCLM :
    (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ((-(2 : ℝ)) • (Sk n).subtypeL).comp (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))
    + ((Matrix.diagonalLinearMap (n := Fin n) (R := ℝ) (α := ℝ)).toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))))
    + ((NN n).subtypeL.comp
        ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))))

@[simp] lemma iwasawaLieMapCLM_apply (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    iwasawaLieMapCLM (X, v, Z) = (-(2 : ℝ)) • X.1 + Matrix.diagonal v + Z.1 := by
  -- Direct computation by unfolding all CLM applications. Every step is `rfl`-equal
  -- (the same `rfl` pattern as Theorem 3's final evaluation).
  rfl

/-- **CLM form of Theorem 3.** The mfderiv of `iwasawaMap` at the
identity equals `iwasawaLieMapCLM` as a CLM equality. Derived from
the pointwise `iwasawaMap_mfderiv_at_one_eq_lieEquiv` by CLM extensionality. -/
theorem mfderiv_iwasawaMap_at_one_eq_lieMapCLM :
    mfderiv ((𝓘(ℝ, (Sk n : Type _))).prod
              ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (iwasawaMap : K n × A n × UU n → G n)
            (⟨1, IsOrthogonal.one⟩, ⟨1, IsPositiveDiagonal.one⟩,
              ⟨1, IsUpperUnipotent.one⟩) =
      iwasawaLieMapCLM := by
  -- Apply CLM extensionality + Theorem 3's pointwise formula.
  apply ContinuousLinearMap.ext
  rintro ⟨X, v, Z⟩
  rw [iwasawaMap_mfderiv_at_one_eq_lieEquiv X v Z]
  exact (iwasawaLieMapCLM_apply X v Z).symm

/-- **The auxiliary `Ad(a)` twist on the source coordinates.** For
`a : A n`, this is the CLM
`(X, v, Z) ↦ (X, v, adNN a Z)` on `Sk n × ((Fin n → ℝ) × NN n)`.
It is retained for the root-density / positive-root determinant
calculation. It is not the full derivative of `iwasawaMap` in the
current right-Cayley chart convention. -/
noncomputable def lieTwistCLM (a : A n) :
    (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ] (Sk n) × ((Fin n → ℝ) × (NN n)) :=
  (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)).prod
    (((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
      ((adNN a).comp
        ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))))

@[simp] lemma lieTwistCLM_apply (a : A n) (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    lieTwistCLM a (X, v, Z) = (X, v, adNN a Z) := rfl

/-! ## L3 explicit factorization (corrected to form (c), matrix Leibniz)

**Convention finding (2026-05-22).** The earlier
stated factorization
`mfderiv = leftMul_{kau} ∘ iwasawaLieMapCLM ∘ lieTwistCLM a` is
INCONSISTENT with our chart conventions. Research confirms the
canonical form for GL_n is the direct matrix-Leibniz formula
(per Knapp Ch. VI, Helgason Ch. II §3 + Ch. IX §1, ANU Andrews
Lecture 5, USTC Wang Lecture 12, KU Copenhagen Iwasawa-for-GL_n notes,
Toronto Meinrenken lecture notes):

  `dμ(δk, δa, δn) = δk · a₀ · n₀ + k₀ · δa · n₀ + k₀ · a₀ · δn`

(The textbook left-translation form `dL_{k₀a₀n₀} ∘ (Ad-twist)` is
equivalent via Ad-conjugation but requires the chart on K to use
left-multiplication, which our `cayleyOpenChartAt Q₀.symm X =
⟨cayley X.1 * Q₀.1, _⟩` does NOT — it uses right-multiplication.)

**Corrected statement (form c).** The CLM `iwasawaMatrixLeibnizCLM k a u`
below packages the direct matrix Leibniz formula. The chart-coord
differentials at general base points are:
- K at k₀: `δX ↦ -2 (δX.1) * k₀.1` (Cayley factor `-2` rides along
  with right-mul by `k₀.1`).
- A at a₀: `δv ↦ a₀.1 * Matrix.diagonal v` (left-mul by `a₀.1` of
  diagonalCLM, since A is positive-diagonal and a₀ commutes with diag).
- UU at u₀: `δZ ↦ δZ.1` (uniformly `NN.subtypeL` since UU chart is
  affine and translation invariant).

Substituted into matrix Leibniz at `(k₀.1, a₀.1, u₀.1)`. -/

/-- The direct matrix-Leibniz CLM at base point `(k, a, u)`, capturing
the manifold differential of `iwasawaMap`. Per Phase 1 research, this
is the canonical form. -/
noncomputable def iwasawaMatrixLeibnizCLM (k : K n) (a : A n) (u : UU n) :
    (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  -- δK term: -2 X.1 * (k.1 * a.1 * u.1) — the Cayley chart right-mul by `k.1`
  -- contributes the `k.1` factor, then `matrix Leibniz` multiplies by `a.1 * u.1`.
  ((-(2 : ℝ)) • ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip
        (k.1 * a.1 * u.1)).comp (Sk n).subtypeL).comp
    (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))
  + -- δA term: k.1 * a.1 * diag(v) * u.1
    (((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) (k.1 * a.1)).comp
        (((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip u.1).comp
          (LinearMap.toContinuousLinearMap
            (Matrix.diagonalLinearMap (Fin n) ℝ ℝ)))).comp
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))))
  + -- δU term: k.1 * a.1 * Z.1
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) (k.1 * a.1)).comp
      ((NN n).subtypeL.comp
        ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))))

@[simp] lemma iwasawaMatrixLeibnizCLM_apply (k : K n) (a : A n) (u : UU n)
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    iwasawaMatrixLeibnizCLM k a u (X, v, Z) =
      (-(2 : ℝ)) • (X.1 * (k.1 * a.1 * u.1)) +
      k.1 * a.1 * Matrix.diagonal v * u.1 +
      k.1 * a.1 * Z.1 := by
  -- Unfold CLM components: add_apply, smul_apply, comp_apply, flip_apply,
  -- mul_apply', fst/snd, subtypeL, diagonalLinearMap.
  simp [iwasawaMatrixLeibnizCLM, ContinuousLinearMap.mul_apply',
    Matrix.diagonalLinearMap_apply, mul_assoc]

/-! ## Layer A: per-direction chart-coord derivative CLMs

Three named CLMs corresponding to the three chart directions
(K via Cayley + right-mul, A via log/exp giving `a₀ * diag`, UU via affine
identity). Each has an `apply` lemma proved by `rfl` (or near-`rfl`).
These isolate the linear-algebra content of L3 from the analytic
differentiability and chart-bookkeeping content. -/

/-- **Layer A1.** The K-direction chart-coord derivative CLM at
base point `k₀ : K n`:
`cayleyRightDerivCLM k₀ X = -2 • (X.1 * k₀.1)`. Built as
`(-2 : ℝ) • (right_mul_by_k₀.1) ∘ (Sk n).subtypeL`. -/
noncomputable def cayleyRightDerivCLM (k₀ : K n) :
    Sk n →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ((-(2 : ℝ)) • ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip k₀.1)).comp
    (Sk n).subtypeL

@[simp] lemma cayleyRightDerivCLM_apply (k₀ : K n) (X : Sk n) :
    cayleyRightDerivCLM k₀ X = (-(2 : ℝ)) • (X.1 * k₀.1) := rfl

/-- **Layer A2.** The A-direction chart-coord derivative CLM at
base point `a₀ : A n`:
`AChartDerivCLM a₀ v = a₀.1 * Matrix.diagonal v`. -/
noncomputable def AChartDerivCLM (a₀ : A n) :
    (Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) a₀.1).comp
    (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ))

@[simp] lemma AChartDerivCLM_apply (a₀ : A n) (v : Fin n → ℝ) :
    AChartDerivCLM a₀ v = a₀.1 * Matrix.diagonal v := rfl

/-- **Layer A3.** The UU-direction chart-coord derivative CLM at
base point `u₀ : UU n`:
`UUChartDerivCLM u₀ Z = Z.1`. Uniformly equal to `(NN n).subtypeL`
since the UU chart is affine. -/
noncomputable def UUChartDerivCLM (_u₀ : UU n) :
    NN n →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (NN n).subtypeL

@[simp] lemma UUChartDerivCLM_apply (u₀ : UU n) (Z : NN n) :
    UUChartDerivCLM u₀ Z = Z.1 := rfl

/-- **Layer A4.** The matrix triple-multiplication derivative CLM at
base point `(K, A, U) : Matrix × Matrix × Matrix`:
`matrixTripleMulDerivCLM K A U (dK, dA, dU) = dK * A * U + K * dA * U + K * A * dU`.

This generalizes `tripleSumCLM` (the at-(1,1,1) version in
IwasawaMFDerivAtOne.lean) to a general base point. -/
noncomputable def matrixTripleMulDerivCLM
    (K_ A_ U_ : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix (Fin n) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  -- dK * A * U
  (((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip (A_ * U_)).comp
    (ContinuousLinearMap.fst ℝ _ _))
  + -- K * dA * U
    (((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) K_).comp
        ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip U_)).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp
        (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ) _)))
  + -- K * A * dU
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) (K_ * A_)).comp
      ((ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ) _).comp
        (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ) _)))

@[simp] lemma matrixTripleMulDerivCLM_apply
    (K_ A_ U_ : Matrix (Fin n) (Fin n) ℝ)
    (dK dA dU : Matrix (Fin n) (Fin n) ℝ) :
    matrixTripleMulDerivCLM K_ A_ U_ (dK, dA, dU) =
      dK * A_ * U_ + K_ * dA * U_ + K_ * A_ * dU := by
  simp only [matrixTripleMulDerivCLM, ContinuousLinearMap.add_apply,
             ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
             ContinuousLinearMap.mul_apply', ContinuousLinearMap.coe_fst',
             ContinuousLinearMap.coe_snd']
  rw [mul_assoc dK A_ U_, mul_assoc K_ dA U_]

/-! ## Layer B (bundled into W3 bridge)

Layer B would contain the ordinary `HasFDerivAt` statements for each
matrix-level chart function:
- B1: `HasFDerivAt (X ↦ cayley X.1 * k₀.1) (cayleyRightDerivCLM k₀) 0`.
- B2: `HasFDerivAt (v ↦ Matrix.diagonal (exp v)) (AChartDerivCLM a₀) (log a₀)`.
- B3: `HasFDerivAt (Z ↦ Z.1 + 1) (UUChartDerivCLM u₀) (u₀.1 - 1)`.
- B4: `HasFDerivAt ((M,N,P) ↦ M*N*P) (matrixTripleMulDerivCLM K A U) (K, A, U)`.

These are proven by direct chain rule + `HasFDerivAt.comp` /
`HasFDerivAt.mul'`. The proofs use `hasFDerivAt_cayley_zero` and
`hasFDerivAt_triple_mul_at_one` from `IwasawaMFDerivAtOne.lean`,
both currently `private`. Re-deriving them locally (~100 lines each)
would be Layer B's content.

The following local lemmas now prove the matrix-level chart
derivatives directly. No bridge axiom is used for
`mfderiv_iwasawaMap_at_factored`. -/

/-! ### Layer B sub-lemmas (matrix-level HasFDerivAt's)

Six atomic sub-lemmas, each proved sorry-free, each compiled before the next.
Per T1-4-L3-DischargeResearch.md §F, these reduce the chart-level computation
to ordinary Fréchet derivatives that can be composed via `HasFDerivAt.comp`. -/

/-- **B1.** `X ↦ cayley X.1 * k₀.1` has Fréchet derivative
`cayleyRightDerivCLM k₀` at `X = 0`. Compose `hasFDerivAt_cayley_zero`
(now public after Step 0) with right-multiplication by `k₀.1`. -/
theorem hasFDerivAt_cayleyRightMul_zero (k₀ : K n) :
    HasFDerivAt (fun X : Sk n => cayley X.1 * k₀.1)
      (cayleyRightDerivCLM k₀) 0 := by
  -- inner: X ↦ X.1 is subtypeL, fderiv = subtypeL.
  have h_subtypeL : HasFDerivAt ((Sk n).subtypeL : Sk n → Matrix _ _ ℝ)
      (Sk n).subtypeL (0 : Sk n) := (Sk n).subtypeL.hasFDerivAt
  -- middle: cayley at 0 has fderiv -2 • id, per `hasFDerivAt_cayley_zero`.
  have h_cay_at0 := hasFDerivAt_cayley_zero (n := n)
  -- Compose: cayley ∘ subtypeL at 0. Match basepoint subtypeL 0 = 0.
  have h_match : (0 : Matrix (Fin n) (Fin n) ℝ) =
      ((Sk n).subtypeL : Sk n → Matrix _ _ ℝ) (0 : Sk n) := by simp
  rw [h_match] at h_cay_at0
  have h_cay_comp := h_cay_at0.comp 0 h_subtypeL
  -- Right-multiplication by k₀.1 is the CLM `(mul ℝ _).flip k₀.1`.
  have h_rmul : HasFDerivAt
      (fun M : Matrix (Fin n) (Fin n) ℝ => M * k₀.1)
      ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip k₀.1)
      (cayley ((Sk n).subtypeL (0 : Sk n))) :=
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip k₀.1).hasFDerivAt
  have h_full := h_rmul.comp 0 h_cay_comp
  -- Match CLM by ext + apply lemma.
  convert h_full using 1
  ext X
  simp [cayleyRightDerivCLM_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
        Submodule.subtypeL_apply,
        MulOpposite.smul_eq_mul_unop]

/-- **B2.** `v ↦ a₀.1 * diagonal (exp ∘ v)` has fderiv `AChartDerivCLM a₀` at `v = 0`.
Per Phase 0 hint: `Real.exp 0 = 1`; lift entry-wise via `hasFDerivAt_pi`; precompose
with `Matrix.diagonal` linear; then left-multiply by `a₀.1` (CLM left-mul, NOT mul_const). -/
theorem hasFDerivAt_AChart_zero (a₀ : A n) :
    HasFDerivAt (fun v : Fin n → ℝ => a₀.1 * Matrix.diagonal (Real.exp ∘ v))
      (AChartDerivCLM a₀) 0 := by
  -- Pi.exp at v=0 has fderiv = id (since exp 0 = 1).
  have h_exp_pi : HasFDerivAt (fun v : Fin n → ℝ => fun i => Real.exp (v i))
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 := by
    rw [hasFDerivAt_pi']
    intro i
    have h_exp : HasDerivAt Real.exp 1 0 := by
      have := Real.hasDerivAt_exp 0
      simpa using this
    have h_fderiv : HasFDerivAt Real.exp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) 1) 0 := h_exp.hasFDerivAt
    have h_proj : HasFDerivAt (fun v : Fin n → ℝ => v i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) 0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
    have h_comp := h_fderiv.comp 0 h_proj
    convert h_comp using 1
    ext v
    simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
          ContinuousLinearMap.id_apply]
  -- Matrix.diagonal is a CLM, fderiv = itself (linear).
  have h_diag : HasFDerivAt (fun w : Fin n → ℝ => Matrix.diagonal w)
      (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ))
      ((fun v : Fin n → ℝ => fun i => Real.exp (v i)) 0) :=
    (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ)).hasFDerivAt
  have h_diag_comp := h_diag.comp 0 h_exp_pi
  -- Left-multiplication by a₀.1 is the CLM (mul ℝ _) a₀.1.
  have h_lmul : HasFDerivAt
      (fun M : Matrix (Fin n) (Fin n) ℝ => a₀.1 * M)
      (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) a₀.1)
      ((fun w : Fin n → ℝ => Matrix.diagonal w)
        ((fun v : Fin n → ℝ => fun i => Real.exp (v i)) 0)) :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) a₀.1).hasFDerivAt
  have h_full := h_lmul.comp 0 h_diag_comp
  convert h_full using 1

/-- **B3.** `Z ↦ Z.1 + 1` has fderiv `UUChartDerivCLM u₀ = (NN n).subtypeL` at `Z = 0`.
Affine: subtypeL + const. -/
theorem hasFDerivAt_UUChart_zero (u₀ : UU n) :
    HasFDerivAt (fun Z : NN n => (Z.1 : Matrix (Fin n) (Fin n) ℝ) + 1)
      (UUChartDerivCLM u₀) 0 := by
  show HasFDerivAt _ ((NN n).subtypeL) 0
  exact ((NN n).subtypeL.hasFDerivAt).add_const (1 : Matrix (Fin n) (Fin n) ℝ)

/-- **B4.** Triple matrix multiplication `(K, A, U) ↦ K * A * U` has
fderiv `matrixTripleMulDerivCLM K₀ A₀ U₀` at `(K₀, A₀, U₀)`. Two
applications of `HasFDerivAt.mul'` on the projection HasFDerivAt's. -/
theorem hasFDerivAt_tripleMul (K₀ A₀ U₀ : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => p.1 * p.2.1 * p.2.2)
      (matrixTripleMulDerivCLM K₀ A₀ U₀) (K₀, A₀, U₀) := by
  have h_fst : HasFDerivAt
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => p.1)
      (ContinuousLinearMap.fst ℝ (Matrix (Fin n) (Fin n) ℝ)
        (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)) (K₀, A₀, U₀) :=
    (ContinuousLinearMap.fst ℝ (Matrix (Fin n) (Fin n) ℝ)
      (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)).hasFDerivAt
  have h_snd_fst : HasFDerivAt
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ)
          (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ))) (K₀, A₀, U₀) :=
    ((ContinuousLinearMap.fst ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ)
        (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ))).hasFDerivAt
  have h_snd_snd : HasFDerivAt
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ)
          (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ))) (K₀, A₀, U₀) :=
    ((ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ)
        (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ))).hasFDerivAt
  have h_inner := h_fst.mul' h_snd_fst
  have h_full := h_inner.mul' h_snd_snd
  -- Rewrite the function on h_full to match the goal: `(f * g) * h ↦ fun p => f p * g p * h p`.
  have h_fun_eq :
      (((fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ => p.1) *
            fun p => p.2.1) *
          fun p => p.2.2) =
        (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
              Matrix (Fin n) (Fin n) ℝ =>
          p.1 * p.2.1 * p.2.2) := by
    funext p; simp [Pi.mul_apply]
  rw [h_fun_eq] at h_full
  -- Now match the CLM: prove `matrixTripleMulDerivCLM K₀ A₀ U₀ = <chained CLM>`.
  convert h_full using 1
  apply ContinuousLinearMap.ext
  rintro ⟨dK, dA, dU⟩
  simp only [matrixTripleMulDerivCLM_apply,
             ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.coe_smul', Pi.smul_apply,
             ContinuousLinearMap.comp_apply,
             ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
             Pi.mul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
             smul_eq_mul]
  noncomm_ring

/-- **B5.** The KAN chart-inverse product `(X, v, Z) ↦ (cayley X * k₀, a₀ * diag(exp v), Z + 1)`
has fderiv = prodMk of three projection-composed CLMs at `(0, 0, 0)`. Built via
`HasFDerivAt.prodMk` applied three-way using B1/B2/B3 precomposed with the
projection CLMs. -/
theorem hasFDerivAt_KAN_chart_zero (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    HasFDerivAt
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * k₀.1,
         a₀.1 * Matrix.diagonal (Real.exp ∘ p.2.1),
         (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
      (((cayleyRightDerivCLM k₀).comp
          (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
        (((AChartDerivCLM a₀).comp
            ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))).prod
          ((UUChartDerivCLM u₀).comp
            ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))))))
      (0, 0, 0) := by
  -- Projection HasFDerivAt's at (0, 0, 0)
  have h_fst : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.1)
      (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)) (0, 0, 0) :=
    (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)).hasFDerivAt
  have h_snd_fst : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.1)
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) (0, 0, 0) :=
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).hasFDerivAt
  have h_snd_snd : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.2)
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) (0, 0, 0) :=
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).hasFDerivAt
  -- B1, B2, B3 at chart coord 0
  have h_K : HasFDerivAt (fun X : Sk n => cayley X.1 * k₀.1)
      (cayleyRightDerivCLM k₀) 0 := hasFDerivAt_cayleyRightMul_zero k₀
  have h_A : HasFDerivAt (fun v : Fin n → ℝ => a₀.1 * Matrix.diagonal (Real.exp ∘ v))
      (AChartDerivCLM a₀) 0 := hasFDerivAt_AChart_zero a₀
  have h_U : HasFDerivAt (fun Z : NN n => (Z.1 : Matrix (Fin n) (Fin n) ℝ) + 1)
      (UUChartDerivCLM u₀) 0 := hasFDerivAt_UUChart_zero u₀
  -- Compose each with the relevant projection. Basepoint of each B is
  -- `proj(0,0,0) = 0`, so the comp lemma's basepoint-matching hypothesis fires.
  have h_K_full := h_K.comp (0 : Sk n × (Fin n → ℝ) × NN n) h_fst
  have h_A_full := h_A.comp (0 : Sk n × (Fin n → ℝ) × NN n) h_snd_fst
  have h_U_full := h_U.comp (0 : Sk n × (Fin n → ℝ) × NN n) h_snd_snd
  -- Three-way product
  exact h_K_full.prodMk (h_A_full.prodMk h_U_full)

/-- **B3 generalized to arbitrary basepoint.** Affine `Z ↦ Z.1 + 1` is its own
derivative `(NN n).subtypeL` at every point. -/
theorem hasFDerivAt_UUChart_at (u₀ : UU n) (Z₀ : NN n) :
    HasFDerivAt (fun Z : NN n => (Z.1 : Matrix (Fin n) (Fin n) ℝ) + 1)
      (UUChartDerivCLM u₀) Z₀ := by
  show HasFDerivAt _ ((NN n).subtypeL) Z₀
  exact ((NN n).subtypeL.hasFDerivAt).add_const (1 : Matrix (Fin n) (Fin n) ℝ)

/-- **B5 generalized to arbitrary UU chart coord.** `(X, v, Z) ↦ (chart_invs)`
has the same product CLM derivative at any `(0, 0, Z₀)` since K/A are linear
and UU is affine. -/
theorem hasFDerivAt_KAN_chart_at (k₀ : K n) (a₀ : A n) (u₀ : UU n) (Z₀ : NN n) :
    HasFDerivAt
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * k₀.1,
         a₀.1 * Matrix.diagonal (Real.exp ∘ p.2.1),
         (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
      (((cayleyRightDerivCLM k₀).comp
          (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
        (((AChartDerivCLM a₀).comp
            ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))).prod
          ((UUChartDerivCLM u₀).comp
            ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))))))
      (0, 0, Z₀) := by
  have h_fst : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.1)
      (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)) (0, 0, Z₀) :=
    (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)).hasFDerivAt
  have h_snd_fst : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.1)
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) (0, 0, Z₀) :=
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).hasFDerivAt
  have h_snd_snd : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.2)
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) (0, 0, Z₀) :=
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).hasFDerivAt
  have h_K : HasFDerivAt (fun X : Sk n => cayley X.1 * k₀.1)
      (cayleyRightDerivCLM k₀) 0 := hasFDerivAt_cayleyRightMul_zero k₀
  have h_A : HasFDerivAt (fun v : Fin n → ℝ => a₀.1 * Matrix.diagonal (Real.exp ∘ v))
      (AChartDerivCLM a₀) 0 := hasFDerivAt_AChart_zero a₀
  have h_U : HasFDerivAt (fun Z : NN n => (Z.1 : Matrix (Fin n) (Fin n) ℝ) + 1)
      (UUChartDerivCLM u₀) Z₀ := hasFDerivAt_UUChart_at u₀ Z₀
  have h_K_full := h_K.comp (0, 0, Z₀) h_fst
  have h_A_full := h_A.comp (0, 0, Z₀) h_snd_fst
  have h_U_full := h_U.comp (0, 0, Z₀) h_snd_snd
  exact h_K_full.prodMk (h_A_full.prodMk h_U_full)

/-- **B6.** The full local iwasawa triple-product `(X, v, Z) ↦
(cayley X * k₀) * (a₀ * diag(exp v)) * (Z + 1)` has fderiv = matrix-Leibniz
formula at chart coord `(0, 0, 0)`, corresponding to manifold point
`(k₀, a₀, ⟨1, IsUpperUnipotent.one⟩)`. Compose B5 with B4 at `(k₀.1, a₀.1, 1)`. -/
theorem hasFDerivAt_iwasawaLocal_zero (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    HasFDerivAt
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * k₀.1) * (a₀.1 * Matrix.diagonal (Real.exp ∘ p.2.1)) *
          ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
      (iwasawaMatrixLeibnizCLM k₀ a₀ ⟨1, IsUpperUnipotent.one⟩)
      (0, 0, 0) := by
  -- B5 at (0, 0, 0): produces (k₀.1, a₀.1, 1) under the chart-inverse triple.
  have h_B5 := hasFDerivAt_KAN_chart_zero k₀ a₀ u₀
  -- B4 at (k₀.1, a₀.1, 1) is matrixTripleMulDerivCLM k₀.1 a₀.1 1.
  have h_B4 :
      HasFDerivAt
        (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
          Matrix (Fin n) (Fin n) ℝ => p.1 * p.2.1 * p.2.2)
        (matrixTripleMulDerivCLM k₀.1 a₀.1 1)
        (k₀.1, a₀.1, 1) :=
    hasFDerivAt_tripleMul k₀.1 a₀.1 1
  -- Match basepoints: B5 at (0,0,0) evaluates to (cayley 0 * k₀.1, a₀.1*1, 0+1)
  -- = (k₀.1, a₀.1, 1). Use `convert` on this elementary value computation.
  have h_basepoint :
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
          (cayley p.1.1 * k₀.1,
           a₀.1 * Matrix.diagonal (Real.exp ∘ p.2.1),
           (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1)) (0, 0, 0) =
        (k₀.1, a₀.1, 1) := by
    show (cayley (0 : Sk n).1 * k₀.1,
          a₀.1 * Matrix.diagonal (Real.exp ∘ (0 : Fin n → ℝ)),
          ((0 : NN n).1 : Matrix (Fin n) (Fin n) ℝ) + 1) =
        (k₀.1, a₀.1, 1)
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
    · -- cayley 0 * k₀.1 = k₀.1
      show (1 - (0 : Matrix (Fin n) (Fin n) ℝ)) * (1 + 0)⁻¹ * k₀.1 = k₀.1
      simp
    · -- a₀.1 * diagonal (exp ∘ 0) = a₀.1
      show a₀.1 * Matrix.diagonal (Real.exp ∘ (0 : Fin n → ℝ)) = a₀.1
      have h1 : (Real.exp ∘ (0 : Fin n → ℝ)) = (1 : Fin n → ℝ) := by
        funext i; simp [Function.comp, Real.exp_zero, Pi.one_apply]
      simp [h1]
    · -- (0 : NN n).1 + 1 = 1
      show ((0 : NN n).1 : Matrix (Fin n) (Fin n) ℝ) + 1 = 1
      simp
  rw [← h_basepoint] at h_B4
  -- Compose B4 with B5 via HasFDerivAt.comp.
  have h_comp := h_B4.comp (0 : Sk n × (Fin n → ℝ) × NN n) h_B5
  -- h_comp's function: `(fun p => p.1 * p.2.1 * p.2.2) ∘ B5_func`
  -- = `fun p => (cayley p.1.1 * k₀.1) * (a₀.1 * diag(exp p.2.1)) * (p.2.2.1 + 1)`.
  -- h_comp's CLM: `matrixTripleMulDerivCLM k₀.1 a₀.1 1 ∘L B5_CLM`.
  -- Match to iwasawaMatrixLeibnizCLM k₀ a₀ ⟨1, _⟩ via convert + ext + simp + noncomm_ring.
  convert h_comp using 1
  apply ContinuousLinearMap.ext
  rintro ⟨X, v, Z⟩
  simp only [iwasawaMatrixLeibnizCLM_apply, ContinuousLinearMap.comp_apply,
             ContinuousLinearMap.prod_apply, cayleyRightDerivCLM_apply,
             AChartDerivCLM_apply, UUChartDerivCLM_apply,
             ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
             matrixTripleMulDerivCLM_apply, smul_eq_mul]
  noncomm_ring

/-- **B6 generalized to general UU chart coord.** The full iwasawa local triple
product, evaluated at chart coord `(0, 0, UU.toNNHomeomorph u₀)` (the chart
coord of `u₀ ∈ UU n` in the singleton chart), has fderiv equal to
`iwasawaMatrixLeibnizCLM k₀ a₀ u₀`. This is the version used by Layer D for
general `u₀`; the L3 lemma at `(k, a, u)` substitutes `u = u₀`. -/
theorem hasFDerivAt_iwasawaLocal_at (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    HasFDerivAt
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * k₀.1) * (a₀.1 * Matrix.diagonal (Real.exp ∘ p.2.1)) *
          ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
      (iwasawaMatrixLeibnizCLM k₀ a₀ u₀)
      (0, 0, UU.toNNHomeomorph u₀) := by
  -- `(UU.toNNHomeomorph u₀).1 = u₀.1 - 1`, so chart-value at UU side is `u₀.1`.
  have hZ₀ : ((UU.toNNHomeomorph u₀).1 : Matrix (Fin n) (Fin n) ℝ) + 1 = u₀.1 := by
    show u₀.1 - 1 + 1 = u₀.1
    abel
  -- B5_at at (0, 0, UU.toNNHomeomorph u₀)
  have h_B5 := hasFDerivAt_KAN_chart_at k₀ a₀ u₀ (UU.toNNHomeomorph u₀)
  -- B4 at chart-value (k₀.1, a₀.1, u₀.1)
  have h_B4 := hasFDerivAt_tripleMul k₀.1 a₀.1 u₀.1
  -- Match basepoint computation.
  have h_basepoint :
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
          (cayley p.1.1 * k₀.1,
           a₀.1 * Matrix.diagonal (Real.exp ∘ p.2.1),
           (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
        (0, 0, UU.toNNHomeomorph u₀) = (k₀.1, a₀.1, u₀.1) := by
    show (cayley (0 : Sk n).1 * k₀.1,
          a₀.1 * Matrix.diagonal (Real.exp ∘ (0 : Fin n → ℝ)),
          ((UU.toNNHomeomorph u₀).1 : Matrix (Fin n) (Fin n) ℝ) + 1) =
        (k₀.1, a₀.1, u₀.1)
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
    · show (1 - (0 : Matrix (Fin n) (Fin n) ℝ)) * (1 + 0)⁻¹ * k₀.1 = k₀.1
      simp
    · show a₀.1 * Matrix.diagonal (Real.exp ∘ (0 : Fin n → ℝ)) = a₀.1
      have h1 : (Real.exp ∘ (0 : Fin n → ℝ)) = (1 : Fin n → ℝ) := by
        funext i; simp [Function.comp, Real.exp_zero, Pi.one_apply]
      simp [h1]
    · exact hZ₀
  rw [← h_basepoint] at h_B4
  have h_comp := h_B4.comp (0, 0, UU.toNNHomeomorph u₀) h_B5
  -- Match CLM via convert + ext + simp + noncomm_ring.
  convert h_comp using 1
  apply ContinuousLinearMap.ext
  rintro ⟨X, v, Z⟩
  simp only [iwasawaMatrixLeibnizCLM_apply, ContinuousLinearMap.comp_apply,
             ContinuousLinearMap.prod_apply, cayleyRightDerivCLM_apply,
             AChartDerivCLM_apply, UUChartDerivCLM_apply,
             ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
             matrixTripleMulDerivCLM_apply, smul_eq_mul]
  noncomm_ring

/-! ## Layer B (actual chart): general-basepoint helpers matching the real chart
structure on A and UU.

B5/B6 (above) encode the A direction as `a₀.1 * diag(exp v)` at basepoint
`v = 0`. The actual `chartAt A a₀` is the singleton chart with symm
`v ↦ ⟨diag(exp v), _⟩` (no `a₀` factor), and `extChartAt A a₀ a₀ = log_diag a₀`
(not 0). This block adds:

* `hasFDerivAt_diagExp_at a₀`: HasFDerivAt `(v ↦ diag(exp v))` at `log_diag a₀`.
* `hasFDerivAt_iwasawaActualLocal_at k₀ a₀ u₀`: HasFDerivAt of the actual
  writtenInExtChartAt form `(cayley X * k₀) * diag(exp v) * (Z + 1)` at the
  chart coord `(0, log_diag a₀, UU.toNN u₀)` with derivative
  `iwasawaMatrixLeibnizCLM k₀ a₀ u₀`. -/

theorem hasFDerivAt_diagExp_at (a₀ : A n) :
    HasFDerivAt (fun v : Fin n → ℝ => Matrix.diagonal (Real.exp ∘ v))
      (AChartDerivCLM a₀) (fun i => Real.log (a₀.1 i i)) := by
  set v₀ : Fin n → ℝ := fun i => Real.log (a₀.1 i i) with hv₀_def
  -- pi_exp at v₀: i-th component derivative scales by `exp(v₀_i) = a₀.1 i i`.
  have h_exp_pi : HasFDerivAt (fun v : Fin n → ℝ => fun i => Real.exp (v i))
      (ContinuousLinearMap.pi (fun i =>
        (Real.exp (v₀ i)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) v₀ := by
    rw [hasFDerivAt_pi']
    intro i
    have h_exp : HasDerivAt Real.exp (Real.exp (v₀ i)) (v₀ i) := Real.hasDerivAt_exp (v₀ i)
    have h_fderiv : HasFDerivAt Real.exp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp (v₀ i))) (v₀ i) :=
      h_exp.hasFDerivAt
    have h_proj : HasFDerivAt (fun v : Fin n → ℝ => v i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) v₀ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
    have h_comp := h_fderiv.comp v₀ h_proj
    convert h_comp using 1
    ext w
    simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
          ContinuousLinearMap.smul_apply, mul_comm]
  -- `Matrix.diagonal` is linear; HasFDerivAt at any point with derivative `diagonalLinearMap`.
  have h_diag : HasFDerivAt (fun w : Fin n → ℝ => Matrix.diagonal w)
      (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ))
      ((fun v : Fin n → ℝ => fun i => Real.exp (v i)) v₀) :=
    (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ)).hasFDerivAt
  have h_full := h_diag.comp v₀ h_exp_pi
  -- Match the resulting composed CLM with `AChartDerivCLM a₀`.
  convert h_full using 1
  apply ContinuousLinearMap.ext
  intro w
  -- Unfold the pi-application: `(pi (fun i => (e i) • proj i)) w = fun i => e i * w i`.
  have h_pi : (ContinuousLinearMap.pi (fun i => (Real.exp (v₀ i)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) w =
      fun i => Real.exp (v₀ i) * w i := by
    funext i
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- Unfold `LinearMap.toContinuousLinearMap diagonalLinearMap`.
  have h_diagLM : ∀ (vec : Fin n → ℝ),
      (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ)) vec =
      Matrix.diagonal vec := fun _ => rfl
  show a₀.1 * Matrix.diagonal w =
      (LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin n) ℝ ℝ))
        ((ContinuousLinearMap.pi (fun i => (Real.exp (v₀ i)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) w)
  rw [h_pi, h_diagLM]
  -- Goal: a₀.1 * Matrix.diagonal w = Matrix.diagonal (fun i => exp(v₀_i) * w_i)
  -- Rewrite exp(v₀_i) = a₀.1 i i, then prove diag-mul-diag identity.
  have h_exp_v₀ : (fun i => Real.exp (v₀ i) * w i) = fun i => a₀.1 i i * w i := by
    funext i
    rw [hv₀_def]
    show Real.exp (Real.log (a₀.1 i i)) * w i = a₀.1 i i * w i
    rw [Real.exp_log (a₀.2.2 i)]
  rw [h_exp_v₀]
  ext i j
  rw [Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, a₀.2.1 i j hij, zero_mul]

/-- **B5 (actual chart).** Product CLM of the three chart-inverse legs at the
chart coord of `(k₀, a₀, u₀)`. Same prodMk-of-three structure as
`hasFDerivAt_KAN_chart_at`, but the A direction uses the actual chart symm
`v ↦ diag(exp v)` (no `a₀.1 *` factor) and the basepoint shifts to
`log_diag a₀`. -/
theorem hasFDerivAt_KAN_actual_at (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    HasFDerivAt
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * k₀.1,
         Matrix.diagonal (Real.exp ∘ p.2.1),
         (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
      (((cayleyRightDerivCLM k₀).comp
          (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
        (((AChartDerivCLM a₀).comp
            ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))).prod
          ((UUChartDerivCLM u₀).comp
            ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
              (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))))))
      (0, (fun i => Real.log (a₀.1 i i)), UU.toNNHomeomorph u₀) := by
  set p₀ : Sk n × (Fin n → ℝ) × NN n :=
    (0, (fun i => Real.log (a₀.1 i i)), UU.toNNHomeomorph u₀) with hp₀_def
  have h_fst : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.1)
      (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)) p₀ :=
    (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)).hasFDerivAt
  have h_snd_fst : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.1)
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) p₀ :=
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).hasFDerivAt
  have h_snd_snd : HasFDerivAt (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.2)
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))) p₀ :=
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).hasFDerivAt
  have h_K : HasFDerivAt (fun X : Sk n => cayley X.1 * k₀.1)
      (cayleyRightDerivCLM k₀) 0 := hasFDerivAt_cayleyRightMul_zero k₀
  have h_A : HasFDerivAt (fun v : Fin n → ℝ => Matrix.diagonal (Real.exp ∘ v))
      (AChartDerivCLM a₀) (fun i => Real.log (a₀.1 i i)) := hasFDerivAt_diagExp_at a₀
  have h_U : HasFDerivAt (fun Z : NN n => (Z.1 : Matrix (Fin n) (Fin n) ℝ) + 1)
      (UUChartDerivCLM u₀) (UU.toNNHomeomorph u₀) :=
    hasFDerivAt_UUChart_at u₀ (UU.toNNHomeomorph u₀)
  have h_K_full := h_K.comp p₀ h_fst
  have h_A_full := h_A.comp p₀ h_snd_fst
  have h_U_full := h_U.comp p₀ h_snd_snd
  exact h_K_full.prodMk (h_A_full.prodMk h_U_full)

/-- **B6 (actual chart).** The triple-mul applied to the actual chart inverses.
HasFDerivAt of `(X, v, Z) ↦ (cayley X * k₀) * diag(exp v) * (Z + 1)` at chart
coord `(0, log_diag a₀, UU.toNN u₀)` with derivative `iwasawaMatrixLeibnizCLM k₀ a₀ u₀`. -/
theorem hasFDerivAt_iwasawaActualLocal_at (k₀ : K n) (a₀ : A n) (u₀ : UU n) :
    HasFDerivAt
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * k₀.1) * Matrix.diagonal (Real.exp ∘ p.2.1) *
          ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
      (iwasawaMatrixLeibnizCLM k₀ a₀ u₀)
      (0, (fun i => Real.log (a₀.1 i i)), UU.toNNHomeomorph u₀) := by
  have h_B5 := hasFDerivAt_KAN_actual_at k₀ a₀ u₀
  have h_B4 := hasFDerivAt_tripleMul k₀.1 a₀.1 u₀.1
  -- Basepoint match: B5 at (0, log_diag a₀, UU.toNN u₀) → (k₀.1, a₀.1, u₀.1).
  have h_basepoint :
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
          (cayley p.1.1 * k₀.1,
           Matrix.diagonal (Real.exp ∘ p.2.1),
           (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1))
        (0, (fun i => Real.log (a₀.1 i i)), UU.toNNHomeomorph u₀) =
        (k₀.1, a₀.1, u₀.1) := by
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩
    · -- cayley 0 * k₀.1 = k₀.1
      show (1 - (0 : Matrix (Fin n) (Fin n) ℝ)) * (1 + 0)⁻¹ * k₀.1 = k₀.1
      simp
    · -- diag(exp ∘ log_diag a₀) = a₀.1: exp(log a₀_ii) = a₀_ii.
      show Matrix.diagonal (Real.exp ∘ (fun i => Real.log (a₀.1 i i))) = a₀.1
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq]
        show Real.exp (Real.log (a₀.1 i i)) = a₀.1 i i
        exact Real.exp_log (a₀.2.2 i)
      · rw [Matrix.diagonal_apply_ne _ hij, a₀.2.1 i j hij]
    · -- (UU.toNN u₀).1 + 1 = u₀.1
      show ((UU.toNNHomeomorph u₀).1 : Matrix (Fin n) (Fin n) ℝ) + 1 = u₀.1
      show u₀.1 - 1 + 1 = u₀.1
      abel
  rw [← h_basepoint] at h_B4
  have h_comp := h_B4.comp (0, (fun i => Real.log (a₀.1 i i)), UU.toNNHomeomorph u₀) h_B5
  -- Match CLM via convert + ext + noncomm_ring.
  convert h_comp using 1
  apply ContinuousLinearMap.ext
  rintro ⟨X, v, Z⟩
  simp only [iwasawaMatrixLeibnizCLM_apply, ContinuousLinearMap.comp_apply,
             ContinuousLinearMap.prod_apply, cayleyRightDerivCLM_apply,
             AChartDerivCLM_apply, UUChartDerivCLM_apply,
             ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
             matrixTripleMulDerivCLM_apply, smul_eq_mul]
  noncomm_ring

/-! ## Layer D: HasMFDerivAt assembly + L3 closure -/

/-- **T1-4 Lemma 3.** The mfderiv of `iwasawaMap` at a general point
`(k, a, u)` is the direct matrix-Leibniz CLM `iwasawaMatrixLeibnizCLM k a u`.

Proof strategy:
1. Establish `HasMFDerivAt (Subtype.val ∘ iwasawaMap) (k,a,u) iwasawaMatrixLeibnizCLM`
   via `hasFDerivAt_iwasawaActualLocal_at` + writtenInExtChartAt unfolding.
2. Chain rule with `Subtype.val_G` (whose mfderiv is `id` on `G n`'s singleton chart)
   to transfer to `mfderiv iwasawaMap (k,a,u)`. -/
theorem mfderiv_iwasawaMap_at_factored (k : K n) (a : A n) (u : UU n) :
    mfderiv ((𝓘(ℝ, (Sk n : Type _))).prod
              ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (iwasawaMap : K n × A n × UU n → G n) (k, a, u) =
      iwasawaMatrixLeibnizCLM k a u := by
  set I_prod := ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _))))) with hI_prod
  set I_M := (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) with hI_M
  set p₀ : K n × A n × UU n := (k, a, u) with hp₀
  -- The matrix-valued composition has HasMFDerivAt with CLM `iwasawaMatrixLeibnizCLM k a u`.
  have h_subVal_iwasawa :
      HasMFDerivAt I_prod I_M
        ((Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘
          (iwasawaMap : K n × A n × UU n → G n))
        p₀ (iwasawaMatrixLeibnizCLM k a u) := by
    refine ⟨?_, ?_⟩
    · -- ContinuousAt
      exact (continuous_subtype_val.continuousAt).comp
        (contMDiff_iwasawaMap.continuous.continuousAt)
    · -- HasFDerivWithinAt
      have h_local := hasFDerivAt_iwasawaActualLocal_at k a u
      have h_chart_coord : extChartAt I_prod p₀ p₀ =
          (0, (fun i => Real.log (a.1 i i)), UU.toNNHomeomorph u) := by
        -- Product extChartAt at p₀ = product of individual extChartAts at their basepoints.
        rw [extChartAt_prod, extChartAt_prod]
        simp only [PartialEquiv.prod_coe, Prod.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · -- chart_K k k = (0 : Sk n) under extChartAt I_Sk (which is just chart since I = id).
          apply Subtype.ext
          show ((cayleyOpenChartAt k) k).1 = 0
          rw [cayleyOpenChartAt_apply_val (self_mem_cayleyOpenChartAt_source k)]
          have hk : k.1 * k.1.transpose = 1 := k.2
          rw [hk]; show (1 - 1 : Matrix (Fin n) (Fin n) ℝ) * (1 + 1)⁻¹ = 0
          rw [sub_self, zero_mul]
        · rfl
        · rfl
      have h_writ_eq :
          writtenInExtChartAt I_prod I_M p₀
              ((Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘
                (iwasawaMap : K n × A n × UU n → G n)) =
            fun p : Sk n × (Fin n → ℝ) × NN n =>
              (cayley p.1.1 * k.1) * Matrix.diagonal (Real.exp ∘ p.2.1) *
                ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1) := by
        funext p
        rfl
      rw [h_writ_eq, h_chart_coord]
      exact h_local.hasFDerivWithinAt
  -- Bridge to mfderiv iwasawaMap via chain rule with Subtype.val_G (singleton chart, mfderiv = id).
  have h_subVal_G_mdiff : MDifferentiableAt I_M I_M
      (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) (iwasawaMap p₀) :=
    mdifferentiableAt_subtypeVal_G _
  have h_iwasawa_mdiff : MDifferentiableAt I_prod I_M
      (iwasawaMap : K n × A n × UU n → G n) p₀ :=
    (contMDiff_iwasawaMap.contMDiffAt).mdifferentiableAt (by decide)
  have h_subVal_G_mfderiv :
      mfderiv I_M I_M (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) (iwasawaMap p₀) =
      ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    mfderiv_subtypeVal_G _
  have h_chain := mfderiv_comp p₀ h_subVal_G_mdiff h_iwasawa_mdiff
  rw [h_subVal_G_mfderiv] at h_chain
  -- h_chain : mfderiv (Subtype.val ∘ iwasawaMap) p₀ = (id ℝ M).comp (mfderiv iwasawaMap p₀)
  -- Simplify away the id.comp factor.
  have h_chain' : mfderiv I_prod I_M
      ((Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ∘
        (iwasawaMap : K n × A n × UU n → G n)) p₀ =
      mfderiv I_prod I_M (iwasawaMap : K n × A n × UU n → G n) p₀ := by
    rw [h_chain]
    exact ContinuousLinearMap.id_comp _
  rw [← h_chain']
  exact h_subVal_iwasawa.mfderiv

end MatrixNormedRing

end IwasawaCoC

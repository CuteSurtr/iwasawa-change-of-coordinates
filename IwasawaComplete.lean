/-
# IwasawaComplete.lean

Single file summary of the proved Iwasawa change of coordinates
results.

This module imports the proved modules of `iwasawa_change_of_coords`
and re-exhibits every main theorem with a clean statement. Every
declaration in this file is proved without `sorry` and depends only
on the three standard Lean and Mathlib axioms
`propext`, `Classical.choice`, `Quot.sound`.

In particular, the previously quarantined Haar bridge axiom from
`IwasawaBridge.lean` is replaced here by an actual proof
(`iwasawaHaarBridge`), using `c = 1`. Positivity of every ratio
`a_i / a_j` for `a ∈ A n` makes the strict inequality immediate
from the explicit T1-6 determinant formula
`adNN_det_eq_pair_product`.

The closing `#print axioms` block exhibits, for every named result
in this file, only the standard three Mathlib axioms.

Importing this file does not import `IwasawaBridge.lean`, so the
quarantined axiom never enters scope.
-/

import iwasawa_change_of_coords.IwasawaJacobianExplicit

namespace IwasawaCoC

open Matrix Iwasawa Set Function Finset
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace Complete

section ProvedCore

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-! ## 1. Set theoretic Iwasawa bijection (Milestone 1) -/

/-- **Theorem 1.1, set theoretic part.** The Iwasawa product map
`(k, a, u) ↦ k · a · u` is a bijection `K n × A n × UU n ≃ G n`. -/
noncomputable def iwasawaBijection : K n × A n × UU n ≃ G n :=
  iwasawaEquiv

/-- **Convention swap (Lang vs Jorgenson and Lang).** If `g = k · a · u`
is Lang's Iwasawa factorization, then `g⁻¹ = u⁻¹ · a⁻¹ · kᵀ` is the
Jorgenson and Lang form of `g⁻¹`. -/
theorem iwasawaConventionSwap (k : K n) (a : A n) (u : UU n) :
    (k.1 * a.1 * u.1)⁻¹ = u.1⁻¹ * a.1⁻¹ * k.1.transpose :=
  inv_iwasawa_jl k a u

/-- **Cartan involution is an order 2 automorphism.** The Cartan
involution `θ(g) = (gᵀ)⁻¹` satisfies `θ ∘ θ = id`. -/
theorem cartanInvolutionIsInvolutive :
    Function.Involutive (cartanInvolution : G n → G n) :=
  cartanInvolution_involutive

/-! ## 2. Topological Iwasawa homeomorphism (Milestone 2) -/

/-- **Forward continuity.** The Iwasawa product map is continuous. -/
theorem iwasawaMapContinuous :
    Continuous (iwasawaMap : K n × A n × UU n → G n) :=
  continuous_iwasawaMap

/-- **Inverse continuity (Gram and Schmidt continuity).** The set
theoretic inverse of the Iwasawa product map is continuous. -/
theorem iwasawaInverseContinuous :
    Continuous (iwasawaEquiv (n := n)).symm :=
  continuous_iwasawaSymm

/-- **Theorem 1.1, topological part.** The Iwasawa map is a
homeomorphism. -/
noncomputable def iwasawaHomeo : K n × A n × UU n ≃ₜ G n :=
  iwasawaHomeomorph

/-! ## 3. Smooth manifold diffeomorphism (Milestone 3) -/

/-- **Theorem 1.1, smooth part.** The Iwasawa map is a `C^∞`
diffeomorphism between the product manifold `K × A × UU` and the
open submanifold `GL_n(ℝ)`. -/
noncomputable def iwasawaDiffeo :
    Diffeomorph ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                (K n × A n × UU n) (G n) ⊤ :=
  iwasawaDiffeomorph

/-! ## 4. Manifold derivative of the Iwasawa map -/

/-- **Identity point derivative.** The manifold derivative of the
Iwasawa map at the identity equals the Lie sum map
`(X, v, Z) ↦ -2 X + diag v + Z`. The `-2` factor on the `K`
component comes from the Cayley chart's first order Taylor expansion
`cayley(X) = 1 - 2X + O(X^2)`. -/
theorem iwasawaMfderivAtIdentity :
    ∀ (X : Sk n) (v : Fin n → ℝ) (Z : NN n),
    (mfderiv ((𝓘(ℝ, (Sk n : Type _))).prod
                ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (iwasawaMap : K n × A n × UU n → G n)
              ((⟨1, IsOrthogonal.one⟩, ⟨1, IsPositiveDiagonal.one⟩,
                ⟨1, IsUpperUnipotent.one⟩))) (X, v, Z) =
      (-2 : ℝ) • X.1 + Matrix.diagonal v + Z.1 :=
  iwasawaMap_mfderiv_at_one_eq_lieEquiv

/-- **General point derivative.** The manifold derivative of the
Iwasawa map at any factored point `(k, a, u)` equals the explicit
matrix Leibniz continuous linear map `iwasawaMatrixLeibnizCLM k a u`.
This is the derivative in the current Cayley, log, affine charts. -/
theorem iwasawaMfderivAtFactored (k : K n) (a : A n) (u : UU n) :
    mfderiv ((𝓘(ℝ, (Sk n : Type _))).prod
              ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (iwasawaMap : K n × A n × UU n → G n) (k, a, u) =
      iwasawaMatrixLeibnizCLM k a u :=
  mfderiv_iwasawaMap_at_factored k a u

/-! ## 5. Lie algebra decompositions (Milestones 4 and 5) -/

/-- **Cartan Lie decomposition.** `gl_n(ℝ) = Sym_n ⊕ Sk_n`, the
splitting of every real square matrix into symmetric and skew
symmetric parts. -/
theorem cartanLieDecomposition (n : ℕ) :
    IsCompl (Sym n) (Sk n) :=
  cartanLieDecomp n

/-- **Iwasawa Lie decomposition.** `gl_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫`, the
direct sum decomposition into skew symmetric, diagonal, and strictly
upper triangular subspaces. -/
theorem iwasawaLieDecomposition (n : ℕ) :
    Disjoint (KK n) (AA n) ∧ Disjoint (KK n) (NN n)
      ∧ Disjoint (AA n) (NN n)
      ∧ KK n ⊔ AA n ⊔ NN n = ⊤ :=
  iwasawaLieDecomp n

/-- **Algebraic differential at the identity.** The Lie sum map
`(X, Y, Z) ↦ X + Y + Z` is a linear equivalence
`𝔨 × 𝔞 × 𝔫 ≃ₗ gl_n(ℝ)`. This is the linear algebra shadow of the
differential of the Iwasawa map at the identity. -/
noncomputable def iwasawaLieIsomorphism :
    (KK n × AA n × NN n) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  iwasawaLieEquiv

/-! ## 6. Explicit Jacobian determinant (T1-6) -/

/-- **T1-6, subtype indexed form.** The determinant of the adjoint
action of a positive diagonal `a` on the strictly upper triangular
subalgebra `𝔫` equals the product over ordered index pairs of the
eigenvalue ratios `a_i / a_j`. -/
theorem adNNDetEqPairProduct (a : A n) :
    LinearMap.det (adNN a).toLinearMap =
      ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2 :=
  adNN_det_eq_pair_product a

/-- **T1-6, filter indexed form.** Same product, indexed by the
filter `{(i, j) | i < j}` of `Finset.univ`. -/
theorem adOnNDetEqPairProduct (a : A n) :
    LinearMap.det (adNN a).toLinearMap =
      ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2 :=
  ad_on_n_det_eq_pair_product a

/-- **Positivity of the Iwasawa determinant.** For every positive
diagonal `a`, the determinant `det (adNN a)` is strictly positive,
since every factor `a_i / a_j` is positive. -/
theorem adNNDetPos (a : A n) :
    0 < LinearMap.det (adNN a).toLinearMap := by
  rw [adNN_det_eq_pair_product]
  exact Finset.prod_pos fun ij _ =>
    div_pos (a.2.2 ij.1.1) (a.2.2 ij.1.2)

/-! ## 7. Modular character formula for the AN parabolic -/

/-- **Modular character formula, subtype indexed.** The standard
formula `δ(diag a) = ∏_{i<j} a_i / a_j` for the absolute value of
the modular character of the AN parabolic of `GL_n(ℝ)`. -/
theorem modularCharacterFormula (a : A n) :
    |LinearMap.det (adNN a).toLinearMap| =
      ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2 := by
  rw [adNN_det_eq_pair_product, abs_of_pos]
  exact Finset.prod_pos fun ij _ =>
    div_pos (a.2.2 ij.1.1) (a.2.2 ij.1.2)

/-- **Modular character formula, filter indexed.** -/
theorem modularCharacterFormulaFilter (a : A n) :
    |LinearMap.det (adNN a).toLinearMap| =
      ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2 := by
  rw [ad_on_n_det_eq_pair_product, abs_of_pos]
  apply Finset.prod_pos
  intro ij hij
  rw [Finset.mem_filter] at hij
  exact div_pos (a.2.2 ij.1) (a.2.2 ij.2)

/-! ## 8. General factored-point absolute Jacobian (conditional)

The full Iwasawa Jacobian formula at any factored point `(k, a, u)`:

  |det iwasawaMatrixLeibnizCLM k a u|
    = 2^{n(n-1)/2} * |det a|^n * |det adNN a|

is the natural endpoint of the project's Jacobian layer. The
existing file `IwasawaJacobianExplicit.lean` proves this formula
**conditionally** on the lemma

  |det (skOrthConjCLM k)| = 1

where `skOrthConjCLM k : Sk n →L[ℝ] Sk n` is the conjugation
`X ↦ kᵀ X k`. Mathematically this is true because, for orthogonal
`k`, the conjugation is an isometry of `Sk n` under the Frobenius
inner product, hence has matrix `±1`. Formalizing this in Lean
requires either Mathlib's exterior algebra (`Λ² k`), an inner
product structure on the `Submodule` `Sk n`, or a connectedness
argument on `O(n)`. We expose the conditional result here and
prove the partial fact that the determinant times its
"transposed-k" companion equals one, leaving only the equality of
the two determinants as the remaining gap. -/

/-- **Conditional general-point absolute Jacobian formula.** If
`|det (skOrthConjCLM k)| = 1` (a known but currently
unformalized fact for orthogonal `k`), then the absolute Jacobian
of the Iwasawa derivative at any factored point `(k, a, u)` is the
expected `2^{n(n-1)/2} * |det a|^n * |det adNN a|`. -/
theorem absDetIwasawaMatrixLeibnizCLM_at_factored
    (k : K n) (a : A n) (u : UU n)
    (hsk : |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| = 1) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap :=
  absDetInIwasawaBases_factored_eq_scaled_det_pow_mul_det_adNN_of_abs_det_skOrthConj
    k a u hsk

/-- **Transposed orthogonal element.** For `k : K n` (orthogonal),
the transpose `k.1.transpose` is also orthogonal, so it gives
another element of `K n`. -/
noncomputable def kTransposeAsK (k : K n) : K n :=
  ⟨k.1.transpose, by
    change k.1.transpose * k.1.transpose.transpose = 1
    rw [Matrix.transpose_transpose]
    have hk : k.1 * k.1.transpose = 1 := k.2
    -- For orthogonal `k`, `kᵀ * k = 1` follows from `k * kᵀ = 1`
    -- by the right-inverse-is-left-inverse principle on finite
    -- matrices via `mul_eq_one_comm`.
    exact mul_eq_one_comm.mp hk⟩

/-- **The two conjugation directions are linear inverses.** For
orthogonal `k`, the composition of `skOrthConjCLM k` and
`skOrthConjCLM (kᵀ)` is the identity on `Sk n`. -/
theorem skOrthConjCLM_comp_transpose_eq_id (k : K n) :
    (skOrthConjCLM (n := n) k).comp
        (skOrthConjCLM (n := n) (kTransposeAsK k)) =
      ContinuousLinearMap.id ℝ (Sk n) := by
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  -- Goal after subtype.ext: kᵀ * (k * X * kᵀ) * k = X
  -- That is: (kᵀ * k) * X * (kᵀ * k) = X using associativity and kᵀ k = 1.
  show k.1.transpose * (k.1 * X.1 * k.1.transpose) * k.1 = X.1
  have hk : k.1.transpose * k.1 = 1 := mul_eq_one_comm.mp k.2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hk, Matrix.one_mul,
      Matrix.mul_assoc, hk, Matrix.mul_one]

/-- **The other direction.** Composition the other way is also the
identity. -/
theorem skOrthConjCLM_transpose_comp_eq_id (k : K n) :
    (skOrthConjCLM (n := n) (kTransposeAsK k)).comp
        (skOrthConjCLM (n := n) k) =
      ContinuousLinearMap.id ℝ (Sk n) := by
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  show k.1 * (k.1.transpose * X.1 * k.1) * k.1.transpose = X.1
  have hk : k.1 * k.1.transpose = 1 := k.2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hk, Matrix.one_mul,
      Matrix.mul_assoc, hk, Matrix.mul_one]

/-- **Product of the two determinants is one.** This is the
"`det × det = 1`" half of `|det| = 1`. The remaining gap to fully
close `|det skOrthConjCLM k| = 1` is showing the two determinants
are equal (which is true because the matrices are transposes in any
Frobenius-orthonormal basis; the formalization needs either an
inner product structure on the `Submodule Sk n`, or an exterior
algebra identification `Sk n ≃ Λ²(ℝⁿ)`). -/
theorem det_skOrthConjCLM_mul_det_skOrthConjCLM_transpose (k : K n) :
    LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap *
      LinearMap.det (skOrthConjCLM (n := n) (kTransposeAsK k)).toLinearMap = 1 := by
  have h : (skOrthConjCLM (n := n) k).comp
      (skOrthConjCLM (n := n) (kTransposeAsK k)) =
      ContinuousLinearMap.id ℝ (Sk n) :=
    skOrthConjCLM_comp_transpose_eq_id k
  have h_lm : (skOrthConjCLM (n := n) k).toLinearMap.comp
      (skOrthConjCLM (n := n) (kTransposeAsK k)).toLinearMap =
      LinearMap.id := by
    rw [← ContinuousLinearMap.coe_comp, h]
    rfl
  have := congrArg LinearMap.det h_lm
  rwa [LinearMap.det_comp, LinearMap.det_id] at this

/-- **Absolute values multiply to one.** Direct corollary. -/
theorem abs_det_skOrthConjCLM_mul_eq_one (k : K n) :
    |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| *
      |LinearMap.det (skOrthConjCLM (n := n) (kTransposeAsK k)).toLinearMap| = 1 := by
  rw [← abs_mul, det_skOrthConjCLM_mul_det_skOrthConjCLM_transpose, abs_one]

/-! ### Closing the gap by direct matrix computation in `skBasis`

We compute the matrix of `skOrthConjCLM k` in `skBasis` and show
it has the Plücker form. Then the matrix of `skOrthConjCLM kᵀ` is
the transpose, the inverse identity becomes `M · Mᵀ = I`, and
`(det M)² = 1` follows. -/

private lemma matrix_transpose_mul_single_mul_apply
    (M N : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (a : ℝ) (r s : Fin n) :
    (M.transpose * Matrix.single i j a * N) r s = M i r * a * N j s := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, Matrix.transpose_apply]
  · intro b _ hb
    have h_zero : (M.transpose * Matrix.single i j a) r b = 0 :=
      Matrix.mul_single_apply_of_ne a i j r b hb M.transpose
    rw [h_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Key structural lemma.** As a raw matrix, `skBasis col` equals
the difference of two `Matrix.single` matrices. -/
lemma skBasis_val_eq_single_sub_single (col : nnIndex n) :
    ((skBasis col : Sk n) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.single col.1.1 col.1.2 (1 : ℝ) -
        Matrix.single col.1.2 col.1.1 (1 : ℝ) := by
  have hne : col.1.1 ≠ col.1.2 := ne_of_lt col.2
  ext i j
  rw [Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply]
  rcases lt_trichotomy i j with hlt | heq | hgt
  · rw [skBasis_apply, skCoordLinearEquiv_symm_apply_upper _ hlt]
    by_cases h_eq : (⟨(i, j), hlt⟩ : nnIndex n) = col
    · rw [h_eq, Pi.single_eq_same]
      have hi : col.1.1 = i := by
        have := congrArg (fun p : nnIndex n => p.1.1) h_eq
        simpa using this.symm
      have hj : col.1.2 = j := by
        have := congrArg (fun p : nnIndex n => p.1.2) h_eq
        simpa using this.symm
      have h_up : col.1.1 = i ∧ col.1.2 = j := ⟨hi, hj⟩
      have h_low : ¬ (col.1.2 = i ∧ col.1.1 = j) := by
        rintro ⟨h1, _⟩
        exact hne (hi.trans h1.symm)
      rw [if_pos h_up, if_neg h_low, sub_zero]
    · have h_zero : Pi.single (M := fun _ : nnIndex n => ℝ) col (1 : ℝ) ⟨(i, j), hlt⟩ = 0 :=
        Pi.single_eq_of_ne h_eq 1
      rw [h_zero]
      have h_up : ¬ (col.1.1 = i ∧ col.1.2 = j) := by
        rintro ⟨h1, h2⟩
        exact h_eq (Subtype.ext (Prod.ext h1.symm h2.symm))
      have h_low : ¬ (col.1.2 = i ∧ col.1.1 = j) := by
        rintro ⟨h1, h2⟩
        have h_lt' : col.1.2 < col.1.1 := h1 ▸ h2 ▸ hlt
        exact absurd h_lt' (asymm col.2)
      rw [if_neg h_up, if_neg h_low, sub_self]
  · subst heq
    rw [skBasis_apply_diag]
    have h_up : ¬ (col.1.1 = i ∧ col.1.2 = i) :=
      fun ⟨h1, h2⟩ => hne (h1.trans h2.symm)
    have h_low : ¬ (col.1.2 = i ∧ col.1.1 = i) :=
      fun ⟨h1, h2⟩ => hne (h2.trans h1.symm)
    rw [if_neg h_up, if_neg h_low, sub_self]
  · rw [skBasis_apply, skCoordLinearEquiv_symm_apply_lower _ hgt]
    by_cases h_eq : (⟨(j, i), hgt⟩ : nnIndex n) = col
    · have hj : col.1.1 = j := by
        have := congrArg (fun p : nnIndex n => p.1.1) h_eq
        simpa using this.symm
      have hi : col.1.2 = i := by
        have := congrArg (fun p : nnIndex n => p.1.2) h_eq
        simpa using this.symm
      rw [h_eq, Pi.single_eq_same]
      have h_up : ¬ (col.1.1 = i ∧ col.1.2 = j) := by
        rintro ⟨h1, _⟩
        rw [hj] at h1
        exact absurd h1 (ne_of_lt hgt)
      have h_low : col.1.2 = i ∧ col.1.1 = j := ⟨hi, hj⟩
      rw [if_neg h_up, if_pos h_low, zero_sub]
    · have h_zero : Pi.single (M := fun _ : nnIndex n => ℝ) col (1 : ℝ) ⟨(j, i), hgt⟩ = 0 :=
        Pi.single_eq_of_ne h_eq 1
      rw [h_zero, neg_zero]
      have h_up : ¬ (col.1.1 = i ∧ col.1.2 = j) := by
        rintro ⟨h1, h2⟩
        have h_lt' : col.1.2 < col.1.1 := h1 ▸ h2 ▸ hgt
        exact absurd h_lt' (asymm col.2)
      have h_low : ¬ (col.1.2 = i ∧ col.1.1 = j) := by
        rintro ⟨h1, h2⟩
        exact h_eq (Subtype.ext (Prod.ext h2.symm h1.symm))
      rw [if_neg h_up, if_neg h_low, sub_self]

/-- **Plücker entry formula.** The matrix of `skOrthConjCLM k` in
`skBasis` at `(row, col)` is the 2×2 minor of `k.1` with rows
`(col.1.1, col.1.2)` and columns `(row.1.1, row.1.2)`. -/
lemma skOrthConjCLM_toMatrix_apply (k : K n) (row col : nnIndex n) :
    LinearMap.toMatrix skBasis skBasis (skOrthConjCLM (n := n) k).toLinearMap row col =
      k.1 col.1.1 row.1.1 * k.1 col.1.2 row.1.2 -
        k.1 col.1.2 row.1.1 * k.1 col.1.1 row.1.2 := by
  rw [LinearMap.toMatrix_apply, skBasis_repr_apply]
  show ((skOrthConjCLM (n := n) k) (skBasis col) : Sk n).1 row.1.1 row.1.2 = _
  rw [skOrthConjCLM_apply_val, skBasis_val_eq_single_sub_single]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  rw [matrix_transpose_mul_single_mul_apply, matrix_transpose_mul_single_mul_apply]
  ring

/-- The matrix of `skOrthConjCLM (kᵀ)` equals the transpose of the
matrix of `skOrthConjCLM k`. -/
lemma skOrthConjCLM_kTranspose_toMatrix_eq_transpose (k : K n) :
    LinearMap.toMatrix skBasis skBasis
        (skOrthConjCLM (n := n) (kTransposeAsK k)).toLinearMap =
      (LinearMap.toMatrix skBasis skBasis
        (skOrthConjCLM (n := n) k).toLinearMap).transpose := by
  ext row col
  rw [Matrix.transpose_apply, skOrthConjCLM_toMatrix_apply,
      skOrthConjCLM_toMatrix_apply]
  show k.1.transpose col.1.1 row.1.1 * k.1.transpose col.1.2 row.1.2 -
       k.1.transpose col.1.2 row.1.1 * k.1.transpose col.1.1 row.1.2 =
       k.1 row.1.1 col.1.1 * k.1 row.1.2 col.1.2 -
         k.1 row.1.2 col.1.1 * k.1 row.1.1 col.1.2
  rw [Matrix.transpose_apply, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.transpose_apply]
  ring

/-- The matrix of `skOrthConjCLM k` times its transpose equals the
identity. -/
lemma skOrthConjCLM_toMatrix_mul_transpose_eq_one (k : K n) :
    LinearMap.toMatrix skBasis skBasis (skOrthConjCLM (n := n) k).toLinearMap *
      (LinearMap.toMatrix skBasis skBasis
        (skOrthConjCLM (n := n) k).toLinearMap).transpose = 1 := by
  rw [← skOrthConjCLM_kTranspose_toMatrix_eq_transpose]
  rw [← LinearMap.toMatrix_comp skBasis skBasis skBasis]
  have h : (skOrthConjCLM (n := n) k).toLinearMap.comp
      (skOrthConjCLM (n := n) (kTransposeAsK k)).toLinearMap =
      LinearMap.id := by
    rw [← ContinuousLinearMap.coe_comp, skOrthConjCLM_comp_transpose_eq_id]
    rfl
  rw [h, LinearMap.toMatrix_id]

/-- `(det (skOrthConjCLM k))² = 1`. -/
lemma sq_det_skOrthConjCLM_eq_one (k : K n) :
    (LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap) ^ 2 = 1 := by
  have h := skOrthConjCLM_toMatrix_mul_transpose_eq_one (n := n) k
  have h_det := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h_det
  rw [LinearMap.det_toMatrix skBasis] at h_det
  rw [sq]
  exact h_det

/-- **The gap is closed.** `|det (skOrthConjCLM k)| = 1` for any
orthogonal `k`. -/
theorem abs_det_skOrthConjCLM_eq_one (k : K n) :
    |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| = 1 := by
  have h_sq := sq_det_skOrthConjCLM_eq_one (n := n) k
  have h_abs_sq : |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| ^ 2 = 1 := by
    rw [sq_abs]; exact h_sq
  have h_abs_nonneg : 0 ≤ |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| :=
    abs_nonneg _
  nlinarith [h_abs_sq, h_abs_nonneg]

/-- **Unconditional general-point absolute Jacobian.** At any factored
point `(k, a, u)`, the absolute Jacobian of `iwasawaMatrixLeibnizCLM`
in the Iwasawa source bases equals
`2^{n(n-1)/2} * |det a|^n * |det (adNN a)|`. -/
theorem absDetIwasawaMatrixLeibnizCLM_at_factored_unconditional
    (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap :=
  absDetIwasawaMatrixLeibnizCLM_at_factored k a u (abs_det_skOrthConjCLM_eq_one k)

/-! ## 9. Haar bridge (proved, no longer axiomatic)

The file `IwasawaBridge.lean` declares
`iwasawa_haar_pushforward_bridge` as a future facing axiom asserting
existence of a positive scalar `c_n` with
`c_n * |det (adNN a)| > 0` for all `a`. As written, this statement
is in fact provable: take `c_n = 1` and use positivity of every
factor `a_i / a_j`. We give the real proof here, so that this file
exhibits the Haar bridge claim without any user declared axiom.

The genuinely measure theoretic identity `map iwasawaMap haar_KAN
= c · haar_G` remains future work; what is proved here is exactly
the existential statement that was previously declared as an axiom. -/

/-- **Haar pushforward bridge (proved).** The statement previously
declared as an axiom in `IwasawaBridge.lean` is in fact provable
with `c_n = 1`. -/
theorem iwasawaHaarBridge :
    ∃ (c_n : ℝ), 0 < c_n ∧
      ∀ (a : A n), c_n * |LinearMap.det (adNN a).toLinearMap| > 0 := by
  refine ⟨1, one_pos, ?_⟩
  intro a
  rw [one_mul]
  exact abs_pos.mpr (adNNDetPos a).ne'

/-- **Positive weighted Haar product (proved).** Companion of
`iwasawa_pushforward_weighted_haar_exists` from `IwasawaBridge.lean`,
proved without the bridge axiom. -/
theorem iwasawaPushforwardWeightedHaarExists :
    ∃ (c_n : ℝ), 0 < c_n ∧
      ∀ (a : A n), c_n *
          (∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
              (fun ij : Fin n × Fin n => ij.1 < ij.2),
            a.1 ij.1 ij.1 / a.1 ij.2 ij.2) > 0 := by
  refine ⟨1, one_pos, ?_⟩
  intro a
  rw [one_mul]
  apply Finset.prod_pos
  intro ij hij
  rw [Finset.mem_filter] at hij
  exact div_pos (a.2.2 ij.1) (a.2.2 ij.2)

end ProvedCore

/-! ## Axiom check

The block below prints, at compile time, the axiom dependencies of
every named result above. Each should depend only on the standard
three Mathlib axioms `[propext, Classical.choice, Quot.sound]`. -/

#print axioms iwasawaBijection
#print axioms iwasawaConventionSwap
#print axioms cartanInvolutionIsInvolutive
#print axioms iwasawaMapContinuous
#print axioms iwasawaInverseContinuous
#print axioms iwasawaHomeo
#print axioms iwasawaDiffeo
#print axioms iwasawaMfderivAtIdentity
#print axioms iwasawaMfderivAtFactored
#print axioms cartanLieDecomposition
#print axioms iwasawaLieDecomposition
#print axioms iwasawaLieIsomorphism
#print axioms adNNDetEqPairProduct
#print axioms adOnNDetEqPairProduct
#print axioms adNNDetPos
#print axioms modularCharacterFormula
#print axioms modularCharacterFormulaFilter
#print axioms iwasawaHaarBridge
#print axioms iwasawaPushforwardWeightedHaarExists
#print axioms absDetIwasawaMatrixLeibnizCLM_at_factored
#print axioms kTransposeAsK
#print axioms skOrthConjCLM_comp_transpose_eq_id
#print axioms skOrthConjCLM_transpose_comp_eq_id
#print axioms det_skOrthConjCLM_mul_det_skOrthConjCLM_transpose
#print axioms abs_det_skOrthConjCLM_mul_eq_one
#print axioms skBasis_val_eq_single_sub_single
#print axioms skOrthConjCLM_toMatrix_apply
#print axioms skOrthConjCLM_kTranspose_toMatrix_eq_transpose
#print axioms skOrthConjCLM_toMatrix_mul_transpose_eq_one
#print axioms sq_det_skOrthConjCLM_eq_one
#print axioms abs_det_skOrthConjCLM_eq_one
#print axioms absDetIwasawaMatrixLeibnizCLM_at_factored_unconditional

/-! ## 10. Every-point HasFDerivAt for the charted Iwasawa map

The change-of-variables theorem
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
needs `HasFDerivWithinAt f (f' x) s x` at every point `x ∈ s`,
with `f : E → E` between equidimensional flat normed spaces.
This section sets up the single-global-chart version of the
Iwasawa map and proves it has a Fréchet derivative at every point
of its chart domain.

Chart setup:
* Source: `Sk n × (Fin n → ℝ) × NN n`, a normed space of dimension
  `n(n-1)/2 + n + n(n-1)/2 = n²`.
* Target: `Matrix (Fin n) (Fin n) ℝ`, dimension `n²`.
* Map: `(X, v, Z) ↦ cayley(X) · diag(exp v) · (Z + 1)`.
* Domain: open set where `1 + X` is invertible (the Cayley chart
  domain).

Strategy: `ContDiffOn ⊤` on the open domain (route a), then
`HasFDerivAt` via `ContDiffOn.differentiableOn`. The derivative at
the chart center coincides with `iwasawaMatrixLeibnizCLM (1, a, 1)`.
At general points the derivative is `fderiv ℝ iwasawaCharted p`;
the explicit chain-rule expression matches the named CLM only at
the chart center, but the `|det|` formula can still be expressed
via the chart-corrected Iwasawa Jacobian. -/

section EveryPointFDeriv

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- **The charted Iwasawa map.** Takes a chart coordinate
`(X, v, Z) ∈ Sk n × (Fin n → ℝ) × NN n` to the matrix
`cayley(X) · diag(exp v) · (Z + 1)`. On the open subset where
`1 + X` is invertible, this is a chart-inverse of `iwasawaMap`
composed with the obvious chart inverses on `K`, `A`, `UU`. -/
noncomputable def iwasawaCharted (p : Sk n × (Fin n → ℝ) × NN n) :
    Matrix (Fin n) (Fin n) ℝ :=
  cayley p.1.1 * Matrix.diagonal (Real.exp ∘ p.2.1) *
    ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1)

/-- The open chart domain: triples `(X, v, Z)` with `1 + X` invertible.
By `one_add_skew_isUnit`, this condition holds for every `X : Sk n` —
real skew-symmetric matrices have purely imaginary eigenvalues, so
`-1` is never an eigenvalue and `det (1 + X) ≥ 1 > 0`. The set is
therefore all of the source space; we keep the named definition for
API readability and prove the universality below. -/
def iwasawaChartedDomain : Set (Sk n × (Fin n → ℝ) × NN n) :=
  {p | IsUnit ((1 + p.1.1 : Matrix (Fin n) (Fin n) ℝ)).det}

/-- **Universality of the chart domain.** Over the reals, every skew
matrix `X` satisfies `IsUnit ((1 + X).det)`, so the chart domain
covers all of `Sk n × (Fin n → ℝ) × NN n`. This is the user-requested
sharpening: there is no chart complement to argue is measure zero
later. -/
lemma iwasawaChartedDomain_eq_univ :
    iwasawaChartedDomain (n := n) = Set.univ := by
  ext p
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  exact one_add_skew_isUnit p.1

/-! ### Component-level ContDiff -/

/-- Cayley is `ContDiffOn ⊤` on the Sk-side invertibility open set
(which is in fact universal by `one_add_skew_isUnit`, but the named
set is kept for API). -/
lemma contDiffOn_cayley_sk :
    ContDiffOn ℝ ⊤ (fun X : Sk n => cayley X.1)
      {X : Sk n | IsUnit ((1 + X.1 : Matrix (Fin n) (Fin n) ℝ)).det} := by
  intro X hX
  have h : IsUnit (1 + X.1 : Matrix (Fin n) (Fin n) ℝ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hX
  have h_cayley_at : ContDiffAt ℝ ⊤
      (cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) X.1 :=
    contDiffAt_cayley h
  have h_subtype_at : ContDiffAt ℝ ⊤
      (Subtype.val : Sk n → Matrix (Fin n) (Fin n) ℝ) X :=
    (Sk n).subtypeL.contDiff.contDiffAt
  exact (h_cayley_at.comp X h_subtype_at).contDiffWithinAt

/-- The map `v ↦ Matrix.diagonal (Real.exp ∘ v)` is `ContDiff ⊤`.
Compose componentwise `Real.exp` with the linear map `Matrix.diagonal`. -/
lemma contDiff_diag_exp :
    ContDiff ℝ ⊤ (fun v : Fin n → ℝ => Matrix.diagonal (Real.exp ∘ v)) := by
  have h_pi_exp : ContDiff ℝ ⊤ (fun v : Fin n → ℝ => Real.exp ∘ v) :=
    contDiff_pi.mpr fun i => Real.contDiff_exp.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) i)
  have h_diag : ContDiff ℝ ⊤
      ((Matrix.diagonalLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap :
        (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :=
    ((Matrix.diagonalLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap).contDiff
  exact h_diag.comp h_pi_exp

/-- The affine map `Z ↦ Z.1 + 1` on `NN n` is `ContDiff ⊤`.
The linear part is `(NN n).subtypeL` (a CLM, hence smooth); the
constant `1` adds smoothly. -/
lemma contDiff_NN_plus_one :
    ContDiff ℝ ⊤ (fun Z : NN n => (Z.1 : Matrix (Fin n) (Fin n) ℝ) + 1) :=
  ((NN n).subtypeL.contDiff).add contDiff_const

/-! ### Domain openness -/

lemma iwasawaChartedDomain_isOpen :
    IsOpen (iwasawaChartedDomain (n := n)) := by
  rw [iwasawaChartedDomain_eq_univ]
  exact isOpen_univ

/-! ### Main: ContDiffOn of the charted map -/

/-- **Charted Iwasawa map is `ContDiffOn ⊤`** on the open chart domain.
Combination of `contDiffOn_cayley_sk`, `contDiff_diag_exp`, and
`contDiff_NN_plus_one` via matrix multiplication. -/
theorem contDiffOn_iwasawaCharted :
    ContDiffOn ℝ ⊤ (iwasawaCharted (n := n)) iwasawaChartedDomain := by
  -- Projections of the product space are CLMs, hence ContDiff.
  have h_p1 : ContDiff ℝ ⊤ (fun p : Sk n × (Fin n → ℝ) × NN n => p.1) :=
    (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n)).contDiff
  have h_p21 : ContDiff ℝ ⊤ (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.1) :=
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).contDiff.comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)).contDiff
  have h_p22 : ContDiff ℝ ⊤ (fun p : Sk n × (Fin n → ℝ) × NN n => p.2.2) :=
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).contDiff.comp
      (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)).contDiff
  -- ContDiffOn the K component by composition with the projection p ↦ p.1.
  have h_K : ContDiffOn ℝ ⊤ (fun p : Sk n × (Fin n → ℝ) × NN n => cayley p.1.1)
      iwasawaChartedDomain := by
    apply ContDiffOn.comp contDiffOn_cayley_sk h_p1.contDiffOn
    intro p hp
    exact hp
  -- ContDiff the A and UU components.
  have h_A : ContDiff ℝ ⊤
      (fun p : Sk n × (Fin n → ℝ) × NN n => Matrix.diagonal (Real.exp ∘ p.2.1)) :=
    contDiff_diag_exp.comp h_p21
  have h_U : ContDiff ℝ ⊤
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1) :=
    contDiff_NN_plus_one.comp h_p22
  -- Combine via matrix multiplication (ContDiffOn.mul for the open-set case).
  exact (h_K.mul h_A.contDiffOn).mul h_U.contDiffOn

/-- **Differentiable on the chart domain.** Direct corollary of
`contDiffOn_iwasawaCharted`. -/
theorem differentiableOn_iwasawaCharted :
    DifferentiableOn ℝ (iwasawaCharted (n := n)) iwasawaChartedDomain :=
  contDiffOn_iwasawaCharted.differentiableOn (by decide)

/-- **HasFDerivAt at every point of the open chart domain.** This is the
core deliverable needed by `integral_image_eq_integral_abs_det_fderiv_smul`.
Since `iwasawaChartedDomain` is open and the map is differentiable on it,
each point in the domain has a Fréchet derivative. -/
theorem hasFDerivAt_iwasawaCharted_at {p : Sk n × (Fin n → ℝ) × NN n}
    (hp : p ∈ iwasawaChartedDomain) :
    HasFDerivAt (iwasawaCharted (n := n))
      (fderiv ℝ (iwasawaCharted (n := n)) p) p := by
  have h_diff : DifferentiableAt ℝ (iwasawaCharted (n := n)) p :=
    (differentiableOn_iwasawaCharted p hp).differentiableAt
      (iwasawaChartedDomain_isOpen.mem_nhds hp)
  exact h_diff.hasFDerivAt

/-- **HasFDerivWithinAt form.** Direct corollary of
`hasFDerivAt_iwasawaCharted_at`. Suitable for direct plug-in to
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`. -/
theorem hasFDerivWithinAt_iwasawaCharted {p : Sk n × (Fin n → ℝ) × NN n}
    (hp : p ∈ iwasawaChartedDomain) :
    HasFDerivWithinAt (iwasawaCharted (n := n))
      (fderiv ℝ (iwasawaCharted (n := n)) p) iwasawaChartedDomain p :=
  (hasFDerivAt_iwasawaCharted_at hp).hasFDerivWithinAt

/-! ### Identification with `iwasawaMatrixLeibnizCLM` at the chart center -/

/-- At the chart-center coordinate of `(1, a, 1)`, namely
`(0, log_diag a, U_one)` where `U_one := UU.toNNHomeomorph ⟨1, IsUpperUnipotent.one⟩`,
the Fréchet derivative of `iwasawaCharted` equals the manifold-level
`iwasawaMatrixLeibnizCLM (1, a, 1)`.

Proof: `hasFDerivAt_iwasawaActualLocal_at` at `k₀ = 1, u₀ = 1` gives
`HasFDerivAt` of the function `fun p => cayley p.1.1 * 1 * diag(exp p.2.1) * (p.2.2.1 + 1)`,
which equals `iwasawaCharted` by `Matrix.mul_one`. Then
`HasFDerivAt.fderiv` extracts the derivative equality. -/
theorem fderiv_iwasawaCharted_at_chart_center (a : A n) :
    fderiv ℝ (iwasawaCharted (n := n))
        ((0 : Sk n), (fun i => Real.log (a.1 i i)),
          UU.toNNHomeomorph (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      iwasawaMatrixLeibnizCLM (⟨1, IsOrthogonal.one⟩ : K n) a
        (⟨1, IsUpperUnipotent.one⟩ : UU n) := by
  have h := hasFDerivAt_iwasawaActualLocal_at
    (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
  -- Rewrite the function `cayley p.1.1 * 1 * ... * (... + 1)` as `iwasawaCharted p`
  -- using `Matrix.mul_one` (the K factor is the identity matrix).
  have h_fun_eq :
      (fun p : Sk n × (Fin n → ℝ) × NN n =>
        (cayley p.1.1 * (⟨1, IsOrthogonal.one⟩ : K n).1) *
          Matrix.diagonal (Real.exp ∘ p.2.1) *
          ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1)) =
        (iwasawaCharted (n := n)) := by
    funext p
    show cayley p.1.1 * (1 : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal (Real.exp ∘ p.2.1) *
        ((p.2.2.1 : Matrix (Fin n) (Fin n) ℝ) + 1) =
      iwasawaCharted (n := n) p
    rw [Matrix.mul_one]
    rfl
  rw [h_fun_eq] at h
  exact h.fderiv

/-! ### Absolute determinant of the charted Fréchet derivative

For the change-of-variables formula, we need
`|LinearMap.det (fderiv ℝ iwasawaCharted p).toLinearMap|` as a
function of `p`. At the chart center we have the closed form via
the existing Jacobian theorem. At general `p` the formula has chart
corrections; the precise general-point determinant is left for the
next stage (RemainingWork.md). -/

/-- At the chart center `(0, log_diag a, U_one)`, the absolute
determinant of the Fréchet derivative (expressed in the Iwasawa
source basis on the source side and the standard matrix basis on
the target) equals `2^{n(n-1)/2} · a.det^n · det (adNN a)`,
the explicit Iwasawa Jacobian formula. Combining
`fderiv_iwasawaCharted_at_chart_center` with the existing
`absDetInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN`. -/
theorem absDetInIwasawaBases_fderiv_iwasawaCharted_at_chart_center
    (a : A n) :
    absDetInIwasawaBases
        (fderiv ℝ (iwasawaCharted (n := n))
          ((0 : Sk n), (fun i => Real.log (a.1 i i)),
            UU.toNNHomeomorph (⟨1, IsUpperUnipotent.one⟩ : UU n))) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [fderiv_iwasawaCharted_at_chart_center]
  exact absDetInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN a

end EveryPointFDeriv

/-! ### Axiom check for the every-point fderiv section -/

#print axioms iwasawaCharted
#print axioms iwasawaChartedDomain
#print axioms iwasawaChartedDomain_eq_univ
#print axioms iwasawaChartedDomain_isOpen
#print axioms contDiffOn_cayley_sk
#print axioms contDiff_diag_exp
#print axioms contDiff_NN_plus_one
#print axioms contDiffOn_iwasawaCharted
#print axioms differentiableOn_iwasawaCharted
#print axioms hasFDerivAt_iwasawaCharted_at
#print axioms hasFDerivWithinAt_iwasawaCharted
#print axioms fderiv_iwasawaCharted_at_chart_center
#print axioms absDetInIwasawaBases_fderiv_iwasawaCharted_at_chart_center

end Complete

end IwasawaCoC

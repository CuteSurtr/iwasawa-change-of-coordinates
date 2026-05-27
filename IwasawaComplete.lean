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

/-! ## 8. Haar bridge (proved, no longer axiomatic)

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

end Complete

end IwasawaCoC

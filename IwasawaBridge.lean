/- 
Quarantined future bridge for the Iwasawa modular-character and
Haar/change-of-variables formulas.

The determinant/product part is now proved directly from the explicit
T1-6 determinant `ad_on_n_det_eq_pair_product`. The remaining bridge is
an explicit future-facing axiom. It is not part of the axiom-clean
diffeomorphism or derivative core.

Per MathlibInfrastructureMap.md §1c "Distribution Haar character":
`Measure.distribHaarChar` is the abstract framework. The Iwasawa-
specific identification with our `adNN` is the bridge.

Per MathlibInfrastructureMap.md §1c "Change of variables": Mathlib's
`integral_image_eq_integral_abs_det_fderiv_smul` is the change-of-
variables formula. The specific identification of the scalar `c` in
`map iwasawaMap (haar_KAN) = c · haar_G` should eventually be proved
from the existing diffeomorphism theorem and the now-proved Jacobian
determinant theorem for `iwasawaMatrixLeibnizCLM`
(`absDetIwasawaMatrixLeibnizCLM_at_factored_unconditional` in
`IwasawaComplete.lean`).
-/

import iwasawa_change_of_coords.IwasawaJacobianExplicit
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace IwasawaCoC

open Matrix Iwasawa Set Function Finset Module MeasureTheory
open scoped Manifold ContDiff RightActions

set_option linter.unusedSectionVars false

variable {n : ℕ}

section Bridges

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Determinant/product bridge theorem

This theorem keeps the old downstream name, but it is no longer an
axiom: it is the absolute-value version of `ad_on_n_det_eq_pair_product`.
The genuinely abstract modular-character identification with
`Measure.distribHaarChar` remains future work. -/
theorem modular_character_A_via_adNN_bridge :
    ∀ (a : A n),
      |LinearMap.det (adNN a).toLinearMap| =
        |∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun ij : Fin n × Fin n => ij.1 < ij.2),
          a.1 ij.1 ij.1 / a.1 ij.2 ij.2| := by
  intro a
  rw [ad_on_n_det_eq_pair_product]

/-! ## Quarantined axiom: Iwasawa Haar pushforward up to scalar

This is intentionally a future-facing placeholder. The current formal
statement only records existence of a positive scalar multiplying the
positive determinant `|det(adNN a)|`; it does not yet state a real
`Measure.map` or integral identity.

The diffeomorphism, derivative, and Jacobian-determinant layers are
all proved: the determinant theorem for the actual derivative
`iwasawaMatrixLeibnizCLM k a u` is
`absDetIwasawaMatrixLeibnizCLM_at_factored_unconditional`
(`IwasawaComplete.lean`). What is still missing is only the
measure-theoretic change-of-variables bridge to Haar measures.

**Mathlib gap.** Per MathlibInfrastructureMap.md §1c "Change of
variables": Mathlib provides `integral_image_eq_integral_abs_det_fderiv_smul`,
but specializing it to the Iwasawa setting requires the full
diffeomorphism + Jacobian chain.

**Literature.** Folland, *A Course in Abstract Harmonic Analysis*
(2nd ed., 2016), Theorem 2.51 and §11.2. Knapp, *Lie Groups Beyond
an Introduction* §VIII.2 (Equation 8.27) for `dg = dk · a^{2ρ} da · dn`.
Helgason, *DGLGSS* Chapter IX §1 Propositions 1.17 and 1.19. -/
axiom iwasawa_haar_pushforward_bridge :
    ∃ (c_n : ℝ), 0 < c_n ∧
      ∀ (a : A n), c_n * |LinearMap.det (adNN a).toLinearMap| > 0

/-! ## Theorem 9: Modular character formula for the AN parabolic

The modular character of the conjugation action of `A` on `N` equals
the explicit product `∏_{i<j} a_i/a_j` (in absolute value).

This combines:
- T1-6 (`ad_on_n_det_eq_pair_product`): the explicit determinant
  formula.
- `modular_character_A_via_adNN_bridge`: the bridge identifying the
  abstract modular character with the absolute determinant.

The result is the standard formula `δ(diag a) = ∏_{i<j} a_i/a_j` for
the modular character of the AN parabolic of `GL_n(ℝ)`.
-/
theorem modular_character_AN_eq_det_ad_on_n (a : A n) :
    |LinearMap.det (adNN a).toLinearMap| =
      |∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2| :=
  modular_character_A_via_adNN_bridge a

/-- The modular character formula in factored form: a positive product
of positive ratios equals its absolute value. This is the explicit
form `δ(diag a) = ∏_{i<j} (a_i/a_j)` (without absolute value, since
all factors are positive when `a` is positive diagonal). -/
theorem modular_character_AN_explicit_form (a : A n) :
    |LinearMap.det (adNN a).toLinearMap| =
      ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2 := by
  rw [modular_character_AN_eq_det_ad_on_n]
  -- |∏ x_i| = ∏ x_i when all x_i > 0. Each x_i = a.1 i i / a.1 j j > 0
  -- since A n is positive diagonal.
  apply abs_of_pos
  apply Finset.prod_pos
  intro ij _
  -- ij = (i, j) with i < j. Both a.1 i i > 0 and a.1 j j > 0.
  have h_num : 0 < a.1 ij.1 ij.1 := a.2.2 ij.1
  have h_den : 0 < a.1 ij.2 ij.2 := a.2.2 ij.2
  exact div_pos h_num h_den

/-! ## Theorem 10 placeholder: positive weighted factor

This theorem is deliberately weaker than a Haar pushforward identity.
Combined with T1-6, it rewrites the quarantined axiom using the explicit
positive-root product `∏_{i<j} a_i/a_j`. A real future replacement
should mention `Measure.map`, product measures, Haar measures, or an
integral change-of-variables formula.

For the full identity `dg = c_n · dk · δ(a) · da · dn` (in standard
notation), see Knapp §VIII.2 or Folland §11.2.
-/
theorem iwasawa_pushforward_weighted_haar_exists :
    ∃ (c_n : ℝ), 0 < c_n ∧
      ∀ (a : A n), c_n * (∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2) > 0 := by
  obtain ⟨c_n, hc_pos, h_prod⟩ := iwasawa_haar_pushforward_bridge (n := n)
  refine ⟨c_n, hc_pos, ?_⟩
  intro a
  have h_eq := modular_character_AN_explicit_form a
  have := h_prod a
  rw [h_eq] at this
  exact this

end Bridges

end IwasawaCoC

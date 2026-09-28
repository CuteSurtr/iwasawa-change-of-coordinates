/-
The positive root product `δ(a) = ∏_{i<j} aᵢ / aⱼ`, stated over the filtered
index set `{(i, j) | i < j} ⊆ Fin n × Fin n`.

This file used to hold the "Haar bridge": a placeholder axiom standing in for
the pushforward of product Haar measure under the Iwasawa map. The axiom only
ever asserted a positivity statement and was removed. The genuine statement,

  `map iwasawaMap (haarK × δ(a) haarA × haarN) = c • haarG`  with  `c > 0`,

together with its integral form and the Jorgenson-Lang ordering, is now proved
in `IwasawaIntegration.lean` (`map_iwasawaMap_haar`, `lintegral_iwasawa`,
`map_iwasawaMapJL_haar`).

What remains here are restatements of `ad_on_n_det_eq_pair_product`: the
determinant of `Ad(a) = (X ↦ a X a⁻¹)` on the strictly upper triangular
matrices is the positive root product. That determinant is also the modular
function of `B = A·N` at `a`; the identification with Mathlib's
`Measure.modularCharacterFun` is `modularCharacterFun_toBB` in
`IwasawaIntegration.lean`.
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

/-- `|det Ad(a)|_𝔫| = |∏_{i<j} aᵢ / aⱼ|`, the absolute value form of
`ad_on_n_det_eq_pair_product`. The name is kept from the version of this file
in which it depended on the placeholder axiom. -/
theorem modular_character_A_via_adNN_bridge :
    ∀ (a : A n),
      |LinearMap.det (adNN a).toLinearMap| =
        |∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun ij : Fin n × Fin n => ij.1 < ij.2),
          a.1 ij.1 ij.1 / a.1 ij.2 ij.2| := by
  intro a
  rw [ad_on_n_det_eq_pair_product]

/-- The same identity as `modular_character_A_via_adNN_bridge`, stated for a
fixed `a`. The left side is the modulus of `Ad(a)` on `𝔫`; see the file header
for how it relates to the modular function of `A·N`. -/
theorem modular_character_AN_eq_det_ad_on_n (a : A n) :
    |LinearMap.det (adNN a).toLinearMap| =
      |∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2| :=
  modular_character_A_via_adNN_bridge a

/-- Without absolute values on the right: every factor `aᵢ / aⱼ` is positive
because `a` is a positive diagonal matrix, so the product is its own absolute
value. -/
theorem modular_character_AN_explicit_form (a : A n) :
    |LinearMap.det (adNN a).toLinearMap| =
      ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ij : Fin n × Fin n => ij.1 < ij.2),
        a.1 ij.1 ij.1 / a.1 ij.2 ij.2 := by
  rw [modular_character_AN_eq_det_ad_on_n]
  apply abs_of_pos
  apply Finset.prod_pos
  intro ij _
  exact div_pos (a.2.2 ij.1) (a.2.2 ij.2)

#print axioms modular_character_A_via_adNN_bridge
#print axioms modular_character_AN_eq_det_ad_on_n
#print axioms modular_character_AN_explicit_form

end Bridges

end IwasawaCoC

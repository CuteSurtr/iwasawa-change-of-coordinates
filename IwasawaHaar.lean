import iwasawa_change_of_coords.IwasawaComplete
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Measure theory layer for the Iwasawa decomposition.

The abstract Haar measures `haarK`, `haarA`, `haarN`, `haarG` on the factor
groups and on `G n` already exist in `IwasawaComplete.lean` (Track B), as
`Measure.haar` with `IsHaarMeasure` instances. This file supplies the
second-countability instances those Haar measures need to be sigma finite,
and builds the product Haar measure on `K n × A n × UU n`.
-/

namespace IwasawaCoC
namespace Complete

open MeasureTheory

variable {n : ℕ}

/-- `Matrix (Fin n) (Fin n) ℝ` is second countable (defeq to the finite
product `Fin n → Fin n → ℝ`). -/
instance instSecondCountableMatrix :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

/-- `NN n` (strictly upper triangular matrices) is second countable, as a
subtype of the second countable `Matrix` space. -/
instance instSecondCountableNN : SecondCountableTopology (NN n) :=
  inferInstanceAs
    (SecondCountableTopology (↥(NN n : Set (Matrix (Fin n) (Fin n) ℝ))))

/-- `A n` is second countable, transported through the log homeomorphism
`A.toFinNRHomeomorph : A n ≃ₜ (Fin n → ℝ)`. -/
instance instSecondCountableA : SecondCountableTopology (A n) :=
  (A.toFinNRHomeomorph (n := n)).secondCountableTopology

/-- `UU n` is second countable, transported through the translation
homeomorphism `UU.toNNHomeomorph : UU n ≃ₜ NN n`. -/
instance instSecondCountableUU : SecondCountableTopology (UU n) :=
  (UU.toNNHomeomorph (n := n)).secondCountableTopology

/-- **Product Haar measure on `K n × A n × UU n`.** The product of the
factor Haar measures `haarK`, `haarA`, `haarN`. It is a Haar measure on the
product group, via `MeasureTheory.Measure.prod.instIsHaarMeasure`. -/
noncomputable def haarKAU : Measure (K n × A n × UU n) :=
  (haarK (n := n)).prod ((haarA (n := n)).prod (haarN (n := n)))

instance instIsHaarMeasureHaarAN :
    ((haarA (n := n)).prod (haarN (n := n))).IsHaarMeasure :=
  inferInstance

instance instIsHaarMeasureHaarKAU : (haarKAU (n := n)).IsHaarMeasure := by
  unfold haarKAU
  infer_instance

/-! ### Explicit left invariant Haar on `A n` via the log chart

The log chart `A.toFinNRHomeomorph : A n ≃ₜ (Fin n → ℝ)` is a group
isomorphism from the multiplicative group `A n` to the additive group
`Fin n → ℝ`. Pushing Lebesgue measure forward through its inverse therefore
gives a left invariant measure on `A n`, an explicit description of Haar on
`A n` (the abstract `haarA` equals it up to a positive scalar). -/

/-- The log chart is a group homomorphism: `φ (D₀ * D) = φ D₀ + φ D`. -/
lemma toFinNRHomeomorph_mul (D₀ D : A n) :
    A.toFinNRHomeomorph (D₀ * D)
      = A.toFinNRHomeomorph D₀ + A.toFinNRHomeomorph D := by
  funext i
  simp only [Pi.add_apply]
  show Real.log ((D₀ * D).1 i i) = Real.log (D₀.1 i i) + Real.log (D.1 i i)
  have hentry : (D₀ * D).1 i i = D₀.1 i i * D.1 i i := by
    show (D₀.1 * D.1) i i = D₀.1 i i * D.1 i i
    rw [Matrix.mul_apply,
      Finset.sum_eq_single i
        (fun k _ hk => by rw [D₀.2.1 i k (Ne.symm hk), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [hentry, Real.log_mul (D₀.2.2 i).ne' (D.2.2 i).ne']

/-- Conjugating left translation by the log chart turns it into additive
translation on `Fin n → ℝ`. -/
lemma toFinNRHomeomorph_symm_mul (D₀ : A n) (v : Fin n → ℝ) :
    D₀ * (A.toFinNRHomeomorph (n := n)).symm v
      = (A.toFinNRHomeomorph (n := n)).symm (A.toFinNRHomeomorph D₀ + v) := by
  have h : A.toFinNRHomeomorph (D₀ * (A.toFinNRHomeomorph (n := n)).symm v)
            = A.toFinNRHomeomorph D₀ + v := by
    rw [toFinNRHomeomorph_mul, Homeomorph.apply_symm_apply]
  rw [← Homeomorph.symm_apply_apply (A.toFinNRHomeomorph (n := n))
        (D₀ * (A.toFinNRHomeomorph (n := n)).symm v), h]

/-- **Explicit Haar on `A n`.** The pushforward of Lebesgue measure on
`Fin n → ℝ` through the inverse log chart. -/
noncomputable def haarAExplicit : Measure (A n) :=
  Measure.map (A.toFinNRHomeomorph (n := n)).symm volume

/-- **`haarAExplicit` is left invariant.** Left translation on `A n` becomes
additive translation in the log chart, and Lebesgue measure is translation
invariant. -/
instance instIsMulLeftInvariantHaarAExplicit :
    (haarAExplicit (n := n)).IsMulLeftInvariant := by
  refine ⟨fun D₀ => ?_⟩
  have hSymm : Measurable (A.toFinNRHomeomorph (n := n)).symm :=
    (A.toFinNRHomeomorph (n := n)).symm.measurable
  have hL : Measurable (fun D : A n => D₀ * D) :=
    (continuous_const.mul continuous_id).measurable
  have hT : Measurable (fun v : Fin n → ℝ => A.toFinNRHomeomorph D₀ + v) :=
    (continuous_const.add continuous_id).measurable
  unfold haarAExplicit
  rw [Measure.map_map hL hSymm]
  have hfun :
      (fun D : A n => D₀ * D) ∘ (A.toFinNRHomeomorph (n := n)).symm
        = (A.toFinNRHomeomorph (n := n)).symm
            ∘ (fun v : Fin n → ℝ => A.toFinNRHomeomorph D₀ + v) := by
    funext v
    simp only [Function.comp_apply]
    exact toFinNRHomeomorph_symm_mul D₀ v
  rw [hfun, ← Measure.map_map hSymm hT, map_add_left_eq_self]

#print axioms haarKAU
#print axioms instIsHaarMeasureHaarKAU
#print axioms toFinNRHomeomorph_mul
#print axioms haarAExplicit
#print axioms instIsMulLeftInvariantHaarAExplicit

end Complete
end IwasawaCoC

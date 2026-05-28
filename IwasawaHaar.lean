import iwasawa_change_of_coords.IwasawaComplete

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

#print axioms haarKAU
#print axioms instIsHaarMeasureHaarKAU

end Complete
end IwasawaCoC

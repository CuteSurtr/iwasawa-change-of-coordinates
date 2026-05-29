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

open MeasureTheory Matrix Iwasawa

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

/-! ### Toward the U conjugation crux

The Haar uniqueness route to the Iwasawa integration formula funnels through
the fact that conjugation `u ↦ a⁻¹ u a` on `UU n` scales the U Haar measure by
a power of `δ(a)`. In exponential (Lie algebra) coordinates the left
translation that pins the U Haar has linear part `1 + N` with `N` nilpotent,
and conjugation is the diagonal map `adNN`. The determinant fact below is the
linear algebra core of that gate: a unipotent endomorphism has determinant one.
See `HaarUniquenessPlan.md` (lemma C4) for the full dependency chain. -/

/-- A unipotent endomorphism (identity plus a nilpotent) has determinant `1`.
This is the determinant input to the left translation Jacobian for the U Haar
measure in the Haar uniqueness route. -/
lemma det_one_add_of_isNilpotent {R M : Type*} [Field R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] {Q : Module.End R M} (hQ : IsNilpotent Q) :
    LinearMap.det ((1 : Module.End R M) + Q) = 1 := by
  have hQpoly : Q.charpoly = (Polynomial.X : Polynomial R) ^ Module.finrank R M :=
    hQ.charpoly_eq_X_pow_finrank
  have hkey : (Polynomial.X : Polynomial R) ^ Module.finrank R M
      = (1 + Q).charpoly.comp (Polynomial.X + Polynomial.C 1) := by
    have h := LinearMap.charpoly_sub_smul (1 + Q) (1 : R)
    rw [one_smul, add_sub_cancel_left, hQpoly] at h
    exact h
  have heval : (1 + Q).charpoly.coeff 0 = (-1 : R) ^ Module.finrank R M := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    have h2 := congrArg (Polynomial.eval (-1 : R)) hkey
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_comp,
               Polynomial.eval_add, Polynomial.eval_C] at h2
    rw [neg_add_cancel] at h2
    exact h2.symm
  rw [LinearMap.det_eq_sign_charpoly_coeff, heval, ← mul_pow]
  norm_num

/-! ### C1: conjugation `u ↦ a⁻¹ u a` as a continuous group automorphism of `U` -/

/-- `a⁻¹ u a` is upper unipotent. Proved by recognizing it, through the public
chart `UU.toNNHomeomorph` and `adNN`, as `1 + (a⁻¹ (u-1) a)` with the bracket
in `NN n`. -/
lemma conjAut_mem (a : A n) (u : UU n) :
    IsUpperUnipotent (a.1⁻¹ * u.1 * a.1) := by
  have hai : a.1⁻¹ * a.1 = 1 :=
    Matrix.nonsing_inv_mul a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  have hainv : (a.1⁻¹)⁻¹ = a.1 :=
    Matrix.nonsing_inv_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  set w : UU n := UU.toNNHomeomorph.symm (adNN a⁻¹ (UU.toNNHomeomorph u)) with hw
  have key : a.1⁻¹ * u.1 * a.1 = w.1 := by
    have e1 : w.1 = ((adNN a⁻¹ (UU.toNNHomeomorph u) : NN n) : Matrix (Fin n) (Fin n) ℝ) + 1 :=
      rfl
    rw [e1, adNN_apply_val, A_coe_inv]
    have e2 : ((UU.toNNHomeomorph u : NN n) : Matrix (Fin n) (Fin n) ℝ) = u.1 - 1 := rfl
    rw [e2, hainv, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hai, sub_add_cancel]
  rw [key]
  exact w.2

/-- `a u a⁻¹` is upper unipotent (the inverse direction of `conjAut`). -/
lemma conjAut_mem' (a : A n) (u : UU n) :
    IsUpperUnipotent (a.1 * u.1 * a.1⁻¹) := by
  have hia : a.1 * a.1⁻¹ = 1 :=
    Matrix.mul_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  set w : UU n := UU.toNNHomeomorph.symm (adNN a (UU.toNNHomeomorph u)) with hw
  have key : a.1 * u.1 * a.1⁻¹ = w.1 := by
    have e1 : w.1 = ((adNN a (UU.toNNHomeomorph u) : NN n) : Matrix (Fin n) (Fin n) ℝ) + 1 :=
      rfl
    rw [e1, adNN_apply_val]
    have e2 : ((UU.toNNHomeomorph u : NN n) : Matrix (Fin n) (Fin n) ℝ) = u.1 - 1 := rfl
    rw [e2, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hia, sub_add_cancel]
  rw [key]; exact w.2

/-- **C1.** Conjugation `u ↦ a⁻¹ u a` is a continuous group automorphism of
`UU n`. -/
noncomputable def conjAut (a : A n) : UU n ≃ₜ* UU n where
  toFun u := ⟨a.1⁻¹ * u.1 * a.1, conjAut_mem a u⟩
  invFun u := ⟨a.1 * u.1 * a.1⁻¹, conjAut_mem' a u⟩
  left_inv u := by
    apply Subtype.ext
    have hia : a.1 * a.1⁻¹ = 1 :=
      Matrix.mul_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
    show a.1 * (a.1⁻¹ * u.1 * a.1) * a.1⁻¹ = u.1
    rw [show a.1 * (a.1⁻¹ * u.1 * a.1) * a.1⁻¹
          = (a.1 * a.1⁻¹) * u.1 * (a.1 * a.1⁻¹) by noncomm_ring, hia, one_mul, mul_one]
  right_inv u := by
    apply Subtype.ext
    have hai : a.1⁻¹ * a.1 = 1 :=
      Matrix.nonsing_inv_mul a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
    show a.1⁻¹ * (a.1 * u.1 * a.1⁻¹) * a.1 = u.1
    rw [show a.1⁻¹ * (a.1 * u.1 * a.1⁻¹) * a.1
          = (a.1⁻¹ * a.1) * u.1 * (a.1⁻¹ * a.1) by noncomm_ring, hai, one_mul, mul_one]
  map_mul' u v := by
    apply Subtype.ext
    have hia : a.1 * a.1⁻¹ = 1 :=
      Matrix.mul_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
    show a.1⁻¹ * (u.1 * v.1) * a.1
        = (a.1⁻¹ * u.1 * a.1) * (a.1⁻¹ * v.1 * a.1)
    rw [show (a.1⁻¹ * u.1 * a.1) * (a.1⁻¹ * v.1 * a.1)
          = a.1⁻¹ * u.1 * (a.1 * a.1⁻¹) * v.1 * a.1 by noncomm_ring, hia]
    noncomm_ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

@[simp] lemma conjAut_apply_val (a : A n) (u : UU n) :
    ((conjAut a u : UU n) : Matrix (Fin n) (Fin n) ℝ) = a.1⁻¹ * u.1 * a.1 := rfl

/-! ### C2: a fresh chart `UU n ≃ₜ (nnIndex n → ℝ)` by strict upper entries -/

/-- The upper unipotent matrix built from strict upper coordinates. -/
def fromCoords (v : nnIndex n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : i < j then v ⟨(i, j), h⟩ else if i = j then 1 else 0

lemma fromCoords_isUpperUnipotent (v : nnIndex n → ℝ) :
    IsUpperUnipotent (fromCoords v) := by
  refine ⟨?_, ?_⟩
  · intro i j hji
    have hji' : j < i := hji
    simp only [fromCoords]
    split_ifs with h1 h2 <;> first | rfl | omega
  · intro i
    simp only [fromCoords]
    split_ifs with h1 h2 <;> first | rfl | omega

/-- **C2.** The chart `UU n ≃ₜ (nnIndex n → ℝ)` reading off strict upper
entries. Built directly in the product topology, so no norm on `NN n` is
needed. -/
def nnChart : UU n ≃ₜ (nnIndex n → ℝ) where
  toFun u := fun ij => u.1 ij.1.1 ij.1.2
  invFun v := ⟨fromCoords v, fromCoords_isUpperUnipotent v⟩
  left_inv u := by
    apply Subtype.ext
    funext i j
    show fromCoords (fun ij => u.1 ij.1.1 ij.1.2) i j = u.1 i j
    simp only [fromCoords]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (u.2.2 i).symm
    · exact (u.2.1 (show j < i by omega)).symm
  right_inv v := by
    funext ij
    show fromCoords v ij.1.1 ij.1.2 = v ij
    simp only [fromCoords]
    exact dif_pos ij.2
  continuous_toFun := by
    apply continuous_pi
    intro ij
    exact (continuous_apply ij.1.2).comp
      ((continuous_apply ij.1.1).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    by_cases hij : i < j
    · have heq : (fun v : nnIndex n → ℝ => fromCoords v i j)
          = fun v => v ⟨(i, j), hij⟩ := by
        funext v; simp only [fromCoords, dif_pos hij]
      rw [heq]; exact continuous_apply _
    · have heq : (fun v : nnIndex n → ℝ => fromCoords v i j)
          = fun _ => (if i = j then (1 : ℝ) else 0) := by
        funext v; simp only [fromCoords, dif_neg hij]
      rw [heq]; exact continuous_const

#print axioms haarKAU
#print axioms instIsHaarMeasureHaarKAU
#print axioms toFinNRHomeomorph_mul
#print axioms haarAExplicit
#print axioms instIsMulLeftInvariantHaarAExplicit
#print axioms det_one_add_of_isNilpotent
#print axioms conjAut_mem
#print axioms conjAut_mem'
#print axioms conjAut
#print axioms conjAut_apply_val
#print axioms fromCoords_isUpperUnipotent
#print axioms nnChart

end Complete
end IwasawaCoC

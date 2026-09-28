import iwasawa_change_of_coords.IwasawaComplete
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Group.ModularCharacter

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
open scoped ENNReal NNReal

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
    split_ifs <;> first | rfl | omega
  · intro i
    simp only [fromCoords]
    split_ifs <;> first | rfl | omega

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
/-! ### C3: conjugation is the diagonal scaling in the chart coordinates -/

/-- In the chart, `conjAut a` multiplies coordinate `ij` by the positive ratio
`(a⁻¹)_{i i} / (a⁻¹)_{j j}` (`= a_j / a_i`). The algebraic heart of the
conjugation scaling: through the chart, `conjAut a` is diagonal, matching
`adNN a⁻¹`. -/
lemma conjAut_nnChart_apply (a : A n) (u : UU n) (ij : nnIndex n) :
    nnChart (conjAut a u) ij
      = ((a⁻¹).1 ij.1.1 ij.1.1 / (a⁻¹).1 ij.1.2 ij.1.2) * nnChart u ij := by
  have hai : a.1⁻¹ * a.1 = 1 :=
    Matrix.nonsing_inv_mul a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  have hainv : (a.1⁻¹)⁻¹ = a.1 :=
    Matrix.nonsing_inv_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  have hne : ij.1.1 ≠ ij.1.2 := ne_of_lt ij.2
  have hval : ((conjAut a u : UU n) : Matrix (Fin n) (Fin n) ℝ)
      = ((adNN a⁻¹ (UU.toNNHomeomorph u) : NN n) : Matrix (Fin n) (Fin n) ℝ) + 1 := by
    rw [conjAut_apply_val, adNN_apply_val, A_coe_inv]
    have e2 : ((UU.toNNHomeomorph u : NN n) : Matrix (Fin n) (Fin n) ℝ) = u.1 - 1 := rfl
    rw [e2, hainv, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hai, sub_add_cancel]
  show ((conjAut a u : UU n) : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2
      = ((a⁻¹).1 ij.1.1 ij.1.1 / (a⁻¹).1 ij.1.2 ij.1.2) * u.1 ij.1.1 ij.1.2
  rw [hval, Matrix.add_apply, Matrix.one_apply_ne hne, add_zero, adNN_entry]
  have e3 : ((UU.toNNHomeomorph u : NN n) : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2
      = u.1 ij.1.1 ij.1.2 := by
    show (u.1 - 1) ij.1.1 ij.1.2 = u.1 ij.1.1 ij.1.2
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
  rw [e3]

#print axioms conjAut
#print axioms conjAut_apply_val
#print axioms fromCoords_isUpperUnipotent
#print axioms nnChart
#print axioms conjAut_nnChart_apply

/-! ### T2: conjugation scaling of the explicit U Haar measure -/

/-- Conjugation ratios on `nnIndex` (`(a⁻¹)_{i i} / (a⁻¹)_{j j}`). -/
noncomputable def conjRatio (a : A n) (ij : nnIndex n) : ℝ :=
  (a⁻¹).1 ij.1.1 ij.1.1 / (a⁻¹).1 ij.1.2 ij.1.2

/-- Conjugation in chart coordinates, as the diagonal linear map. -/
noncomputable def conjDiag (a : A n) : (nnIndex n → ℝ) →ₗ[ℝ] (nnIndex n → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (conjRatio a))

lemma conjDiag_apply (a : A n) (w : nnIndex n → ℝ) (ij : nnIndex n) :
    conjDiag a w ij = conjRatio a ij * w ij := by
  simp only [conjDiag, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma det_conjDiag_prod (a : A n) :
    LinearMap.det (conjDiag a) = ∏ ij : nnIndex n, conjRatio a ij := by
  rw [conjDiag, LinearMap.det_toLin', Matrix.det_diagonal]

/-- `det (adNN a) > 0` (a product of positive ratios). -/
lemma det_adNN_pos (a : A n) : 0 < LinearMap.det (adNN a).toLinearMap := by
  rw [adNN_det_eq_pair_product]
  apply Finset.prod_pos
  intro ij _
  exact div_pos (a.2.2 ij.1.1) (a.2.2 ij.1.2)

/-- `adNN a (adNN a⁻¹ X) = X` (pointwise). -/
lemma adNN_adNN_inv (a : A n) (X : NN n) : adNN a (adNN a⁻¹ X) = X := by
  have hia : a.1 * a.1⁻¹ = 1 :=
    Matrix.mul_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  have hainv : (a.1⁻¹)⁻¹ = a.1 :=
    Matrix.nonsing_inv_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')
  apply Subtype.ext
  show ((adNN a (adNN a⁻¹ X) : NN n) : Matrix (Fin n) (Fin n) ℝ) = (X : Matrix (Fin n) (Fin n) ℝ)
  rw [adNN_apply_val, adNN_apply_val, A_coe_inv, hainv,
      show a.1 * (a.1⁻¹ * X.1 * a.1) * a.1⁻¹
        = (a.1 * a.1⁻¹) * X.1 * (a.1 * a.1⁻¹) by noncomm_ring, hia, one_mul, mul_one]

/-- `adNN a` composed with `adNN a⁻¹` is the identity on `NN n`. -/
lemma adNN_comp_adNN_inv (a : A n) :
    (adNN a).toLinearMap ∘ₗ (adNN a⁻¹).toLinearMap = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  exact adNN_adNN_inv a X

/-- `det (adNN a⁻¹) = (det adNN a)⁻¹`. -/
lemma det_adNN_inv (a : A n) :
    LinearMap.det (adNN a⁻¹).toLinearMap = (LinearMap.det (adNN a).toLinearMap)⁻¹ := by
  have hd : LinearMap.det ((adNN a).toLinearMap ∘ₗ (adNN a⁻¹).toLinearMap) = 1 := by
    rw [adNN_comp_adNN_inv, LinearMap.det_id]
  rw [LinearMap.det_comp] at hd
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hd)

/-- `det (conjDiag a) = (det adNN a)⁻¹`. -/
lemma det_conjDiag (a : A n) :
    LinearMap.det (conjDiag a) = (LinearMap.det (adNN a).toLinearMap)⁻¹ := by
  rw [det_conjDiag_prod, ← det_adNN_inv, adNN_det_eq_pair_product]
  rfl

/-- The chart conjugate of `conjAut a` is the diagonal map `conjDiag a`. -/
lemma conjAut_nnChart_symm (a : A n) (w : nnIndex n → ℝ) :
    conjAut a (nnChart.symm w) = nnChart.symm (conjDiag a w) := by
  apply nnChart.injective
  rw [Homeomorph.apply_symm_apply]
  funext ij
  rw [conjAut_nnChart_apply, Homeomorph.apply_symm_apply, conjDiag_apply]
  rfl

/-- **The explicit `U` Haar measure**: the pushforward of Lebesgue measure on
the chart coordinates through the inverse chart. -/
noncomputable def nuU : Measure (UU n) := Measure.map nnChart.symm volume

/-- **T2.** Pushing the explicit `U` measure forward along
`conjAut a : u ↦ a⁻¹ u a` multiplies it by `δ(a) = det (adNN a)`:
`map (conjAut a) nuU = δ(a) • nuU`. The determinant
half of the crux, via the chart and the additive Haar determinant scaling. -/
lemma map_conjAut_nuU (a : A n) :
    Measure.map (conjAut a) (nuU (n := n))
      = ENNReal.ofReal (LinearMap.det (adNN a).toLinearMap) • nuU := by
  have hmConj : Measurable (conjAut a) := (conjAut a).continuous.measurable
  have hmChart : Measurable (nnChart (n := n)).symm := (nnChart (n := n)).symm.measurable
  have hmDiag : Measurable (conjDiag a) :=
    (conjDiag a).continuous_of_finiteDimensional.measurable
  have hfun : (⇑(conjAut a)) ∘ (⇑(nnChart (n := n)).symm)
      = (⇑(nnChart (n := n)).symm) ∘ (⇑(conjDiag a)) := by
    funext w; exact conjAut_nnChart_symm a w
  have hdne : LinearMap.det (conjDiag a) ≠ 0 := by
    rw [det_conjDiag]; exact inv_ne_zero (det_adNN_pos a).ne'
  unfold nuU
  rw [Measure.map_map hmConj hmChart, hfun, ← Measure.map_map hmChart hmDiag,
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdne, Measure.map_smul]
  congr 1
  rw [det_conjDiag, inv_inv, abs_of_pos (det_adNN_pos a)]

#print axioms det_adNN_pos
#print axioms det_adNN_inv
#print axioms det_conjDiag
#print axioms conjAut_nnChart_symm
#print axioms map_conjAut_nuU

/-! ### T1: strictly upper triangular matrices are nilpotent -/

/-- **T1.** A strictly upper triangular matrix (a member of `NN n`) is
nilpotent. Via the upper triangular characteristic polynomial `X ^ n` and
Cayley-Hamilton. -/
lemma nn_isNilpotent (Y : NN n) : IsNilpotent Y.1 := by
  have hbt : Y.1.BlockTriangular id := fun i j hji => Y.2 i j (le_of_lt hji)
  have hdiag : ∀ i, Y.1 i i = 0 := fun i => Y.2 i i le_rfl
  have hcp : Y.1.charpoly = (Polynomial.X : Polynomial ℝ) ^ Fintype.card (Fin n) := by
    rw [Matrix.charpoly_of_upperTriangular Y.1 hbt]
    simp only [hdiag, map_zero, sub_zero, Finset.prod_const, Finset.card_univ]
  refine ⟨Fintype.card (Fin n), ?_⟩
  have hch := Y.1.aeval_self_charpoly
  rw [hcp, map_pow, Polynomial.aeval_X] at hch
  exact hch

#print axioms nn_isNilpotent

/-! ### T3: left invariance of `nuU` (the gate) -/

/-- The strict upper matrix built from coordinates (the linear part of
`fromCoords`, with no diagonal `1`). -/
def coordMat (w : nnIndex n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : i < j then w ⟨(i, j), h⟩ else 0

lemma coordMat_mem (w : nnIndex n → ℝ) : coordMat w ∈ NN n := by
  intro i j hji
  simp only [coordMat]
  rw [dif_neg (by omega : ¬ i < j)]

/-- The product of two strict upper triangular matrices is strict upper
triangular. -/
lemma nn_mul_mem (Y X : NN n) : Y.1 * X.1 ∈ NN n := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases lt_or_ge i k with hik | hik
  · rcases lt_or_ge k j with hkj | hkj
    · omega
    · rw [X.2 k j hkj, mul_zero]
  · rw [Y.2 i k hik, zero_mul]

/-- The linear isomorphism `NN n ≃ₗ (nnIndex n → ℝ)` reading off strict upper
entries (the linear core of the chart). -/
def nnCoordEquiv : NN n ≃ₗ[ℝ] (nnIndex n → ℝ) where
  toFun X := fun ij => X.1 ij.1.1 ij.1.2
  map_add' X X' := by funext ij; simp only [Submodule.coe_add, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by funext ij; simp only [SetLike.val_smul, Matrix.smul_apply, Pi.smul_apply,
    RingHom.id_apply, smul_eq_mul]
  invFun w := ⟨coordMat w, coordMat_mem w⟩
  left_inv X := by
    apply Subtype.ext
    funext i j
    show coordMat (fun ij => X.1 ij.1.1 ij.1.2) i j = X.1 i j
    simp only [coordMat]
    split_ifs with h
    · rfl
    · exact (X.2 i j (by omega)).symm
  right_inv w := by
    funext ij
    show coordMat w ij.1.1 ij.1.2 = w ij
    simp only [coordMat]
    exact dif_pos ij.2

@[simp] lemma nnCoordEquiv_apply (X : NN n) (ij : nnIndex n) :
    nnCoordEquiv X ij = X.1 ij.1.1 ij.1.2 := rfl

@[simp] lemma nnCoordEquiv_symm_val (w : nnIndex n → ℝ) :
    ((nnCoordEquiv.symm w : NN n) : Matrix (Fin n) (Fin n) ℝ) = coordMat w := rfl

#print axioms nn_mul_mem
#print axioms nnCoordEquiv

/-- Left multiplication by a strict upper `Y` as an endomorphism of `NN n`. -/
def leftMulNN (Y : NN n) : NN n →ₗ[ℝ] NN n where
  toFun X := ⟨Y.1 * X.1, nn_mul_mem Y X⟩
  map_add' X X' := by
    apply Subtype.ext
    show Y.1 * (X + X' : NN n).1 = Y.1 * X.1 + Y.1 * X'.1
    rw [Submodule.coe_add, Matrix.mul_add]
  map_smul' c X := by
    apply Subtype.ext
    show Y.1 * (c • X : NN n).1 = c • (Y.1 * X.1)
    rw [SetLike.val_smul, Matrix.mul_smul]

@[simp] lemma leftMulNN_apply_val (Y X : NN n) :
    ((leftMulNN Y X : NN n) : Matrix (Fin n) (Fin n) ℝ) = Y.1 * X.1 := rfl

lemma leftMulNN_pow_apply_val (Y : NN n) (m : ℕ) (X : NN n) :
    (((leftMulNN Y) ^ m) X : Matrix (Fin n) (Fin n) ℝ) = Y.1 ^ m * X.1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, leftMulNN_apply_val, ih, pow_succ', Matrix.mul_assoc]

/-- `leftMulNN Y` is nilpotent (from `Y` being nilpotent, T1). -/
lemma leftMulNN_isNilpotent (Y : NN n) : IsNilpotent (leftMulNN Y) := by
  obtain ⟨m, hm⟩ := nn_isNilpotent Y
  refine ⟨m, ?_⟩
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  rw [show (((leftMulNN Y) ^ m) X : NN n) = (((leftMulNN Y) ^ m) X) from rfl]
  show (((leftMulNN Y) ^ m) X : Matrix (Fin n) (Fin n) ℝ) = ((0 : NN n →ₗ[ℝ] NN n) X : NN n)
  rw [leftMulNN_pow_apply_val, hm, Matrix.zero_mul]
  rfl

#print axioms leftMulNN
#print axioms leftMulNN_isNilpotent

/-- The linear part of left translation in chart coordinates: the conjugate
of the unipotent `1 + leftMulNN Y` by `nnCoordEquiv`. -/
noncomputable def transLin (Y : NN n) : (nnIndex n → ℝ) →ₗ[ℝ] (nnIndex n → ℝ) :=
  nnCoordEquiv.toLinearMap ∘ₗ ((1 : Module.End ℝ (NN n)) + leftMulNN Y) ∘ₗ
      nnCoordEquiv.symm.toLinearMap

/-- The linear part has determinant `1` (it is conjugate to a unipotent). -/
lemma det_transLin (Y : NN n) : LinearMap.det (transLin Y) = 1 := by
  rw [transLin, LinearMap.det_conj]
  exact det_one_add_of_isNilpotent (leftMulNN_isNilpotent Y)

lemma transLin_apply (Y : NN n) (w : nnIndex n → ℝ) (ij : nnIndex n) :
    transLin Y w ij = w ij + (Y.1 * coordMat w) ij.1.1 ij.1.2 := by
  have h1 : transLin Y w
      = nnCoordEquiv (nnCoordEquiv.symm w + leftMulNN Y (nnCoordEquiv.symm w)) := by
    simp only [transLin, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply,
      Module.End.one_apply]
  rw [h1, map_add, Pi.add_apply, nnCoordEquiv_apply, nnCoordEquiv_apply, leftMulNN_apply_val,
    nnCoordEquiv_symm_val]
  congr 1
  show coordMat w ij.1.1 ij.1.2 = w ij
  simp only [coordMat]; exact dif_pos ij.2

#print axioms det_transLin
#print axioms transLin_apply

lemma fromCoords_eq (w : nnIndex n → ℝ) : fromCoords w = coordMat w + 1 := by
  funext i j
  simp only [fromCoords, coordMat, Matrix.add_apply, Matrix.one_apply]
  split_ifs <;> first | omega | ring

lemma u_mul_fromCoords (u₀ : UU n) (w : nnIndex n → ℝ) :
    u₀.1 * fromCoords w = (u₀.1 - 1) * coordMat w + coordMat w + u₀.1 := by
  rw [fromCoords_eq]; noncomm_ring

/-- **Affine decomposition of left translation in chart coordinates.** Left
multiplication by `u₀` on `U`, transported by the chart, is the affine map
`w ↦ transLin (u₀ - 1) w + nnChart u₀`. -/
lemma leftMul_nnChart_symm (u₀ : UU n) (w : nnIndex n → ℝ) :
    u₀ * nnChart.symm w
      = nnChart.symm (transLin (UU.toNNHomeomorph u₀) w + nnChart u₀) := by
  apply nnChart.injective
  rw [Homeomorph.apply_symm_apply]
  funext ij
  have hcm : coordMat w ij.1.1 ij.1.2 = w ij := by
    simp only [coordMat]; exact dif_pos ij.2
  rw [Pi.add_apply, transLin_apply]
  show (u₀.1 * fromCoords w) ij.1.1 ij.1.2
      = (w ij + ((u₀.1 - 1) * coordMat w) ij.1.1 ij.1.2) + u₀.1 ij.1.1 ij.1.2
  rw [u_mul_fromCoords, Matrix.add_apply, Matrix.add_apply, hcm]
  ring

#print axioms fromCoords_eq
#print axioms leftMul_nnChart_symm

/-- The linear part preserves volume (determinant `1`). -/
lemma map_transLin_volume (Y : NN n) :
    Measure.map (transLin Y) (volume : Measure (nnIndex n → ℝ)) = volume := by
  have hne : LinearMap.det (transLin Y) ≠ 0 := by rw [det_transLin]; norm_num
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, det_transLin]
  simp

/-- The affine map `w ↦ transLin Y w + c` preserves volume (linear part has
determinant `1`, plus translation invariance). -/
lemma map_transAffine_volume (Y : NN n) (c : nnIndex n → ℝ) :
    Measure.map (fun w => transLin Y w + c) (volume : Measure (nnIndex n → ℝ)) = volume := by
  have hf : (fun w => transLin Y w + c) = (fun x => x + c) ∘ (transLin Y) := by funext w; rfl
  rw [hf, ← Measure.map_map (measurable_add_const c)
      (transLin Y).continuous_of_finiteDimensional.measurable,
      map_transLin_volume, map_add_right_eq_self]

/-- **T3.** The explicit `U` measure `nuU` is left invariant, hence a left
Haar measure on `U`. -/
instance instIsMulLeftInvariant_nuU : (nuU (n := n)).IsMulLeftInvariant := by
  refine ⟨fun u₀ => ?_⟩
  have hmL : Measurable (fun u : UU n => u₀ * u) :=
    (continuous_const.mul continuous_id).measurable
  have hmChart : Measurable (nnChart (n := n)).symm := (nnChart (n := n)).symm.measurable
  have hmAff : Measurable
      (fun w : nnIndex n → ℝ => transLin (UU.toNNHomeomorph u₀) w + nnChart u₀) :=
    ((transLin (UU.toNNHomeomorph u₀)).continuous_of_finiteDimensional.measurable).add_const _
  have hcomp : (fun u : UU n => u₀ * u) ∘ (nnChart (n := n)).symm
      = (nnChart (n := n)).symm
          ∘ (fun w => transLin (UU.toNNHomeomorph u₀) w + nnChart u₀) := by
    funext w; exact leftMul_nnChart_symm u₀ w
  unfold nuU
  rw [Measure.map_map hmL hmChart, hcomp, ← Measure.map_map hmChart hmAff,
      map_transAffine_volume]

#print axioms map_transLin_volume
#print axioms instIsMulLeftInvariant_nuU

/-- `nuU` is finite on compacts (pushforward of `volume` via the chart). -/
instance instIsFiniteOnCompacts_nuU : IsFiniteMeasureOnCompacts (nuU (n := n)) := by
  refine ⟨fun K hK => ?_⟩
  have hpre : (nnChart (n := n)).symm ⁻¹' K = (nnChart (n := n)) '' K := by
    ext w
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      exact ⟨(nnChart (n := n)).symm w, h, (nnChart (n := n)).apply_symm_apply w⟩
    · rintro ⟨u, hu, rfl⟩
      rwa [Homeomorph.symm_apply_apply]
  unfold nuU
  rw [Measure.map_apply (nnChart (n := n)).symm.measurable hK.measurableSet, hpre]
  exact (hK.image (nnChart (n := n)).continuous).measure_lt_top

/-- `nuU` is positive on opens (pushforward of `volume` via the chart). -/
instance instIsOpenPos_nuU : (nuU (n := n)).IsOpenPosMeasure :=
  (nnChart (n := n)).symm.continuous.isOpenPosMeasure_map (nnChart (n := n)).symm.surjective

/-- `nuU` is regular (pushforward of the regular `volume` via the chart). -/
instance instRegular_nuU : (nuU (n := n)).Regular :=
  Measure.Regular.map (nnChart (n := n)).symm

/-- `nuU` is a Haar measure on `U` (left invariant, finite on compacts,
positive on opens). -/
instance instIsHaarMeasure_nuU : (nuU (n := n)).IsHaarMeasure := ⟨⟩

#print axioms instIsHaarMeasure_nuU

/-! ### T4: the crux — the Haar character of `u ↦ a⁻¹ u a` is `δ(a)⁻¹`

Equivalently, pushing Haar measure on `U` forward along `u ↦ a⁻¹ u a`
multiplies it by `δ(a)` (`map_conjAut_haarN`). -/

/-- **T4 — the crux**, `ℝ≥0` form. Combining the determinant scaling (T2,
`map_conjAut_nuU`) with `nuU` being a regular Haar measure (T3), the Haar
character of conjugation is `δ(a)⁻¹`:
`mulEquivHaarChar (conjAut a) = (det (adNN a))⁻¹`. -/
lemma mulEquivHaarChar_conjAut_eq_toNNReal_inv (a : A n) :
    mulEquivHaarChar (conjAut a)
      = (Real.toNNReal (LinearMap.det (adNN a).toLinearMap))⁻¹ := by
  have hδnn : Real.toNNReal (LinearMap.det (adNN a).toLinearMap) ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero]; exact not_le.mpr (det_adNN_pos a)
  haveI : Measure.IsHaarMeasure
      ((LinearMap.det (adNN a).toLinearMap).toNNReal • nuU (n := n)) :=
    Measure.IsHaarMeasure.nnreal_smul (nuU (n := n)) hδnn
  have hmap : Measure.map (conjAut a) (nuU (n := n))
      = Real.toNNReal (LinearMap.det (adNN a).toLinearMap) • nuU := by
    rw [map_conjAut_nuU a]
    exact Measure.coe_nnreal_smul _ nuU
  rw [mulEquivHaarChar_eq nuU (conjAut a)]
  simp only [hmap]
  have hkey := Measure.mul_haarScalarFactor_smul (nuU (n := n)) (nuU (n := n)) hδnn
  rw [Measure.haarScalarFactor_self] at hkey
  exact eq_inv_of_mul_eq_one_right hkey

/-- **T4 — the crux**, real form: `mulEquivHaarChar (conjAut a) = δ(a)⁻¹`,
where `δ(a) = det (adNN a) = ∏_{i<j} a_i / a_j`. -/
lemma mulEquivHaarChar_conjAut (a : A n) :
    (mulEquivHaarChar (conjAut a) : ℝ) = (LinearMap.det (adNN a).toLinearMap)⁻¹ := by
  rw [mulEquivHaarChar_conjAut_eq_toNNReal_inv a, NNReal.coe_inv,
      Real.coe_toNNReal _ (det_adNN_pos a).le]

#print axioms mulEquivHaarChar_conjAut

/-! ### The crux for the canonical Haar measure `haarN` -/

/-- **Crux, canonical form.** Pushing the abstract Haar measure
`haarN = Measure.haar` on `U` forward along `conjAut a : u ↦ a⁻¹ u a`
multiplies it by `δ(a) = det (adNN a)`:
`map (conjAut a) haarN = δ(a) • haarN`. This transports T4 from the explicit
chart measure `nuU` to the project's canonical Haar measure, since
`mulEquivHaarChar` does not depend on the chosen regular Haar measure. -/
lemma map_conjAut_haarN (a : A n) :
    Measure.map (conjAut a) (haarN (n := n))
      = (LinearMap.det (adNN a).toLinearMap).toNNReal • haarN := by
  have hδnn : (LinearMap.det (adNN a).toLinearMap).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero]; exact not_le.mpr (det_adNN_pos a)
  have h := mulEquivHaarChar_smul_map (haarN (n := n)) (conjAut a)
  rw [mulEquivHaarChar_conjAut_eq_toNNReal_inv a] at h
  have h2 := congrArg (fun μ : Measure (UU n) =>
      (LinearMap.det (adNN a).toLinearMap).toNNReal • μ) h
  simpa only [smul_smul, mul_inv_cancel₀ hδnn, one_smul] using h2

#print axioms map_conjAut_haarN

/-! ### Determinant of matrix multiplication maps (toward GL_n Haar)

Left/right multiplication by a fixed matrix `g` on the matrix space
`Matrix (Fin n) (Fin n) ℝ` is `ℝ`-linear with determinant `(det g) ^ n`
(each of the `n` columns/rows is transformed by `g`). Proved column/row-wise
via `LinearMap.det_pi`; purely algebraic, no normed structure needed. -/

/-- Left multiplication `M ↦ g * M` as an `ℝ`-linear endomorphism of the
matrix space. -/
def leftMulMatLin (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun M := g * M
  map_add' M N := mul_add g M N
  map_smul' c M := mul_smul_comm c g M

/-- Right multiplication `M ↦ M * g` as an `ℝ`-linear endomorphism of the
matrix space. -/
def rightMulMatLin (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun M := M * g
  map_add' M N := add_mul M N g
  map_smul' c M := smul_mul_assoc c M g

/-- Right multiplication, row-by-row, is the `n`-fold diagonal map applying
`Matrix.toLin' gᵀ` to each row. -/
lemma rightMulMatLin_eq_pi (g : Matrix (Fin n) (Fin n) ℝ) :
    rightMulMatLin g
      = LinearMap.pi (fun i : Fin n => (Matrix.toLin' gᵀ).comp (LinearMap.proj i)) := by
  refine LinearMap.ext fun M => funext fun i => ?_
  show (M * g) i = Matrix.toLin' gᵀ (M i)
  rw [Matrix.toLin'_apply, Matrix.mulVec_transpose, Matrix.mul_apply_eq_vecMul]

/-- `det (M ↦ M * g) = (det g) ^ n`. -/
lemma det_rightMulMatLin (g : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (rightMulMatLin g) = (Matrix.det g) ^ n := by
  have key : LinearMap.det (rightMulMatLin g)
      = ∏ _i : Fin n, LinearMap.det (Matrix.toLin' gᵀ) := by
    rw [rightMulMatLin_eq_pi]
    exact LinearMap.det_pi _
  rw [key, LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Matrix.det_transpose]

/-- Left multiplication, conjugated by transpose, is right multiplication by
`gᵀ`: `(·ᵀ) ∘ (g * ·) ∘ (·ᵀ) = (· * gᵀ)`. -/
lemma leftMul_conj_eq_rightMul (g : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ : _ →ₗ[ℝ] _) ∘ₗ
        (leftMulMatLin g) ∘ₗ
        ((Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).symm : _ →ₗ[ℝ] _)
      = rightMulMatLin gᵀ := by
  refine LinearMap.ext fun M => ?_
  ext i k
  show ((g * Mᵀ)ᵀ) i k = (M * gᵀ) i k
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `det (M ↦ g * M) = (det g) ^ n`. -/
lemma det_leftMulMatLin (g : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (leftMulMatLin g) = (Matrix.det g) ^ n := by
  rw [← LinearMap.det_conj (leftMulMatLin g) (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ),
    leftMul_conj_eq_rightMul, det_rightMulMatLin, Matrix.det_transpose]

/-- **Algebraic unimodularity core.** Conjugation `M ↦ g * M * g⁻¹` by an
invertible matrix `g` has determinant `1` on the matrix space, since
`det (Lₘ ∘ R_{g⁻¹}) = (det g)^n · (det g⁻¹)^n = 1`. This is the linear-algebra
reason `GL_n(ℝ)` is unimodular (the adjoint action preserves volume). -/
lemma det_conjMatLin (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    LinearMap.det ((leftMulMatLin g).comp (rightMulMatLin g⁻¹)) = 1 := by
  rw [LinearMap.det_comp, det_leftMulMatLin, det_rightMulMatLin, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', ← mul_pow, mul_inv_cancel₀ hg, one_pow]

#print axioms det_leftMulMatLin
#print axioms det_rightMulMatLin
#print axioms det_conjMatLin

/-! ### GL_n Haar: coordinate space Lebesgue scaling

Following the `nuU` technique, the measure work is done on the coordinate space
`(Fin n × Fin n) → ℝ` (which carries Lebesgue `volume`, an additive Haar
measure) rather than on `Matrix` directly (which has a measurable space diamond
and no global normed structure). Left/right multiplication by a fixed invertible
matrix, transported to the coordinate space, scales `volume` by `|det g|^(-n)`
(from `det_leftMulMatLin` / `det_rightMulMatLin` via `LinearMap.det_conj` and
`map_linearMap_addHaar_eq_smul_addHaar`). -/

/-- The coordinate chart `Matrix ≃ₗ (Fin n × Fin n → ℝ)` (uncurry), used to
place Lebesgue `volume` on the matrix space without a measurable space diamond. -/
noncomputable def matrixToCoord :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] ((Fin n × Fin n) → ℝ) :=
  (LinearEquiv.curry ℝ ℝ (Fin n) (Fin n)).symm

/-- Left multiplication `M ↦ g * M` transported to the coordinate space. -/
noncomputable def leftMulCoord (g : Matrix (Fin n) (Fin n) ℝ) :
    ((Fin n × Fin n) → ℝ) →ₗ[ℝ] ((Fin n × Fin n) → ℝ) :=
  matrixToCoord.conj (leftMulMatLin g)

/-- Right multiplication `M ↦ M * g` transported to the coordinate space. -/
noncomputable def rightMulCoord (g : Matrix (Fin n) (Fin n) ℝ) :
    ((Fin n × Fin n) → ℝ) →ₗ[ℝ] ((Fin n × Fin n) → ℝ) :=
  matrixToCoord.conj (rightMulMatLin g)

/-- `det (leftMulCoord g) = (det g) ^ n`. -/
lemma det_leftMulCoord (g : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (leftMulCoord g) = (Matrix.det g) ^ n := by
  have h : LinearMap.det (leftMulCoord g) = LinearMap.det (leftMulMatLin g) :=
    LinearMap.det_conj (leftMulMatLin g) matrixToCoord
  rw [h, det_leftMulMatLin]

/-- `det (rightMulCoord g) = (det g) ^ n`. -/
lemma det_rightMulCoord (g : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (rightMulCoord g) = (Matrix.det g) ^ n := by
  have h : LinearMap.det (rightMulCoord g) = LinearMap.det (rightMulMatLin g) :=
    LinearMap.det_conj (rightMulMatLin g) matrixToCoord
  rw [h, det_rightMulMatLin]

/-- Left multiplication by an invertible `g` scales coordinate Lebesgue by
`|det g|^(-n)`. -/
lemma map_leftMulCoord_volume (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Measure.map (leftMulCoord g) (volume : Measure ((Fin n × Fin n) → ℝ))
      = ENNReal.ofReal |((Matrix.det g) ^ n)⁻¹| • volume := by
  have hdet : LinearMap.det (leftMulCoord g) ≠ 0 := by
    rw [det_leftMulCoord]; exact pow_ne_zero n hg
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, det_leftMulCoord]

/-- Right multiplication by an invertible `g` scales coordinate Lebesgue by
`|det g|^(-n)`. -/
lemma map_rightMulCoord_volume (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Measure.map (rightMulCoord g) (volume : Measure ((Fin n × Fin n) → ℝ))
      = ENNReal.ofReal |((Matrix.det g) ^ n)⁻¹| • volume := by
  have hdet : LinearMap.det (rightMulCoord g) ≠ 0 := by
    rw [det_rightMulCoord]; exact pow_ne_zero n hg
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, det_rightMulCoord]

#print axioms map_leftMulCoord_volume
#print axioms map_rightMulCoord_volume

/-! ### GL_n Haar: lintegral change of variables

Integrating against coordinate Lebesgue, precomposition with left/right
multiplication by an invertible `g` picks up the factor `|det g|^(-n)`. -/

/-- Normalize `|((det g)^n)⁻¹|` (the Lebesgue scaling factor) to the clean
density form `(|det g|^n)⁻¹`. -/
private lemma abs_detPow_inv (g : Matrix (Fin n) (Fin n) ℝ) :
    |((Matrix.det g) ^ n)⁻¹| = (|g.det| ^ n)⁻¹ := by
  rw [abs_inv, abs_pow]

/-- Change of variables for left multiplication. -/
lemma lintegral_leftMulCoord (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0)
    {F : ((Fin n × Fin n) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (leftMulCoord g x) ∂(volume : Measure ((Fin n × Fin n) → ℝ))
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * ∫⁻ x, F x ∂volume := by
  rw [← lintegral_map hF (leftMulCoord g).continuous_of_finiteDimensional.measurable,
    map_leftMulCoord_volume g hg, lintegral_smul_measure, smul_eq_mul, abs_detPow_inv]

/-- Change of variables for right multiplication. -/
lemma lintegral_rightMulCoord (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0)
    {F : ((Fin n × Fin n) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (rightMulCoord g x) ∂(volume : Measure ((Fin n × Fin n) → ℝ))
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * ∫⁻ x, F x ∂volume := by
  rw [← lintegral_map hF (rightMulCoord g).continuous_of_finiteDimensional.measurable,
    map_rightMulCoord_volume g hg, lintegral_smul_measure, smul_eq_mul, abs_detPow_inv]

#print axioms lintegral_leftMulCoord
#print axioms lintegral_rightMulCoord

/-! ### GL_n Haar: the explicit bi invariant density measure

The `GL_n` Haar density `|det g|^(-n)` in coordinates, with its transformation
laws under left/right multiplication, and the resulting bi invariance of the
measure `volume.withDensity detWeightCoord` under multiplication by an
invertible matrix. -/

/-- The `GL_n` Haar density `|det g|^(-n)` at the coordinate point `w`
(`g = matrixToCoord.symm w`). -/
noncomputable def detWeightCoord (w : (Fin n × Fin n) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((|(matrixToCoord.symm w).det| ^ n)⁻¹)

/-- `det ∘ matrixToCoord.symm` is continuous (`det` is a polynomial in the
entries, and the chart is linear on a finite dimensional space). -/
lemma continuous_det_matrixToCoord_symm :
    Continuous (fun w : (Fin n × Fin n) → ℝ => (matrixToCoord.symm w).det) :=
  (matrixToCoord.symm.toLinearMap.continuous_of_finiteDimensional).matrix_det

/-- The density `detWeightCoord` is measurable. -/
lemma measurable_detWeightCoord :
    Measurable (detWeightCoord (n := n)) := by
  unfold detWeightCoord
  exact (((continuous_det_matrixToCoord_symm.abs.pow n).measurable).inv).ennreal_ofReal

/-- Density transformation under left multiplication: precomposing with
`leftMulCoord g` multiplies the density by `|det g|^(-n)`. -/
lemma detWeightCoord_leftMulCoord (g : Matrix (Fin n) (Fin n) ℝ)
    (w : (Fin n × Fin n) → ℝ) :
    detWeightCoord (leftMulCoord g w)
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * detWeightCoord w := by
  have hsymm : matrixToCoord.symm (leftMulCoord g w) = g * matrixToCoord.symm w := by
    rw [leftMulCoord, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  unfold detWeightCoord
  rw [hsymm, Matrix.det_mul, abs_mul, mul_pow, mul_inv,
    ENNReal.ofReal_mul (by positivity)]

/-- Density transformation under right multiplication. -/
lemma detWeightCoord_rightMulCoord (g : Matrix (Fin n) (Fin n) ℝ)
    (w : (Fin n × Fin n) → ℝ) :
    detWeightCoord (rightMulCoord g w)
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * detWeightCoord w := by
  have hsymm : matrixToCoord.symm (rightMulCoord g w) = matrixToCoord.symm w * g := by
    rw [rightMulCoord, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  unfold detWeightCoord
  rw [hsymm, Matrix.det_mul, abs_mul, mul_pow, mul_inv,
    ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal ((|(matrixToCoord.symm w).det| ^ n)⁻¹))]

/-- **The explicit `GL_n` Haar measure**, on the coordinate space: Lebesgue
weighted by the density `|det g|^(-n)`. -/
noncomputable def haarGCoord : Measure ((Fin n × Fin n) → ℝ) :=
  volume.withDensity (detWeightCoord (n := n))

#print axioms measurable_detWeightCoord
#print axioms detWeightCoord_leftMulCoord
#print axioms detWeightCoord_rightMulCoord

/-! ### GL_n Haar: bi invariance (measure level unimodularity)

The measure `haarGCoord = volume.withDensity detWeightCoord` is invariant under
both left and right multiplication by an invertible matrix: the `|det g|^(-n)`
Lebesgue scaling (step 1) cancels the `|det g|^(-n)` density factor (step 3).
This is the linear-algebra heart of `GL_n(ℝ)` unimodularity. -/

/-- The `|det g|^(-n)` factor is nonzero (for invertible `g`). -/
private lemma ofReal_detFactor_ne_zero (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    ENNReal.ofReal ((|g.det| ^ n)⁻¹) ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  exact inv_pos.mpr (pow_pos (abs_pos.mpr hg) n)

/-- **Left invariance** of the explicit `GL_n` Haar measure. -/
lemma map_leftMulCoord_haarGCoord (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Measure.map (leftMulCoord g) (haarGCoord (n := n)) = haarGCoord := by
  have hcont : Measurable (leftMulCoord g) :=
    (leftMulCoord g).continuous_of_finiteDimensional.measurable
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hFL : Measurable (fun a => F (leftMulCoord g a)) := hF.comp hcont
  rw [lintegral_map hF hcont]
  unfold haarGCoord
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_detWeightCoord hFL,
    lintegral_withDensity_eq_lintegral_mul _ measurable_detWeightCoord hF]
  simp only [Pi.mul_apply]
  -- Goal: ∫ dW a * F (leftMul a) = ∫ dW a * F a.
  -- Change of variables on `H = fun a => dW a * F a` gives the factor |det g|^(-n).
  have hcov : ∫⁻ x, detWeightCoord (n := n) (leftMulCoord g x) * F (leftMulCoord g x) ∂volume
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * ∫⁻ x, detWeightCoord x * F x ∂volume := by
    have h := lintegral_leftMulCoord g hg (measurable_detWeightCoord.mul hF)
    simpa only [Pi.mul_apply] using h
  -- The density transformation also pulls out that factor.
  have htrans : ∫⁻ x, detWeightCoord (n := n) (leftMulCoord g x) * F (leftMulCoord g x) ∂volume
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹)
        * ∫⁻ x, detWeightCoord x * F (leftMulCoord g x) ∂volume := by
    rw [← lintegral_const_mul _ (measurable_detWeightCoord.mul hFL)]
    refine lintegral_congr fun x => ?_
    rw [detWeightCoord_leftMulCoord, mul_assoc]
  -- Combine and cancel the positive finite factor.
  have key : ENNReal.ofReal ((|g.det| ^ n)⁻¹)
      * ∫⁻ x, detWeightCoord (n := n) x * F (leftMulCoord g x) ∂volume
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * ∫⁻ x, detWeightCoord x * F x ∂volume := by
    rw [← htrans, hcov]
  exact (ENNReal.mul_right_inj (ofReal_detFactor_ne_zero g hg)
    ENNReal.ofReal_ne_top).mp key

/-- **Right invariance** of the explicit `GL_n` Haar measure. -/
lemma map_rightMulCoord_haarGCoord (g : Matrix (Fin n) (Fin n) ℝ) (hg : g.det ≠ 0) :
    Measure.map (rightMulCoord g) (haarGCoord (n := n)) = haarGCoord := by
  have hcont : Measurable (rightMulCoord g) :=
    (rightMulCoord g).continuous_of_finiteDimensional.measurable
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hFR : Measurable (fun a => F (rightMulCoord g a)) := hF.comp hcont
  rw [lintegral_map hF hcont]
  unfold haarGCoord
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_detWeightCoord hFR,
    lintegral_withDensity_eq_lintegral_mul _ measurable_detWeightCoord hF]
  simp only [Pi.mul_apply]
  have hcov : ∫⁻ x, detWeightCoord (n := n) (rightMulCoord g x) * F (rightMulCoord g x) ∂volume
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * ∫⁻ x, detWeightCoord x * F x ∂volume := by
    have h := lintegral_rightMulCoord g hg (measurable_detWeightCoord.mul hF)
    simpa only [Pi.mul_apply] using h
  have htrans : ∫⁻ x, detWeightCoord (n := n) (rightMulCoord g x) * F (rightMulCoord g x) ∂volume
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹)
        * ∫⁻ x, detWeightCoord x * F (rightMulCoord g x) ∂volume := by
    rw [← lintegral_const_mul _ (measurable_detWeightCoord.mul hFR)]
    refine lintegral_congr fun x => ?_
    rw [detWeightCoord_rightMulCoord, mul_assoc]
  have key : ENNReal.ofReal ((|g.det| ^ n)⁻¹)
      * ∫⁻ x, detWeightCoord (n := n) x * F (rightMulCoord g x) ∂volume
      = ENNReal.ofReal ((|g.det| ^ n)⁻¹) * ∫⁻ x, detWeightCoord x * F x ∂volume := by
    rw [← htrans, hcov]
  exact (ENNReal.mul_right_inj (ofReal_detFactor_ne_zero g hg)
    ENNReal.ofReal_ne_top).mp key

#print axioms map_leftMulCoord_haarGCoord
#print axioms map_rightMulCoord_haarGCoord

/-! ### GL_n Haar: the chart `gToCoord : G n → coordinate space`

To transport the explicit bi invariant measure `haarGCoord` from the
coordinate space to `G n = GL_n(ℝ)`, we use the chart `g ↦ matrixToCoord g.1`.
Following the project rule that the matrix space carries no norm, we do **not**
build a homeomorphism or a continuous linear equivalence on it. Instead we view
`matrixToCoord` as a *measurable* equivalence between the two Pi style
measurable spaces (`Matrix = Fin n → Fin n → ℝ` and `Fin n × Fin n → ℝ`,
measurable both ways through `continuous_of_finiteDimensional`), and compose it
with the measurable embedding `Subtype.val : G n → Matrix` of the open subtype
`{ g // g.det ≠ 0 }`. A `MeasurableEmbedding` is all that the comap needs. -/

/-- `matrixToCoord` as a measurable equivalence (measurable both ways, since a
linear map between finite dimensional real spaces is continuous). -/
noncomputable def matrixToCoordMeasEquiv :
    Matrix (Fin n) (Fin n) ℝ ≃ᵐ ((Fin n × Fin n) → ℝ) where
  toEquiv := matrixToCoord.toEquiv
  measurable_toFun :=
    matrixToCoord.toLinearMap.continuous_of_finiteDimensional.measurable
  measurable_invFun :=
    matrixToCoord.symm.toLinearMap.continuous_of_finiteDimensional.measurable

/-- The invertible locus `{ g | g.det ≠ 0 }` is measurable (`det` is
continuous, so it is the preimage of the open set `{0}ᶜ`). -/
lemma measurableSet_det_ne_zero :
    MeasurableSet {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  have hdet : Measurable fun g : Matrix (Fin n) (Fin n) ℝ => g.det :=
    continuous_id.matrix_det.measurable
  exact hdet (measurableSet_singleton (0 : ℝ)).compl

/-- The chart from `G n` (invertible matrices) to the coordinate space. -/
noncomputable def gToCoord (g : G n) : (Fin n × Fin n) → ℝ := matrixToCoord g.1

/-- `gToCoord` is a measurable embedding: the measurable equivalence
`matrixToCoordMeasEquiv` composed with the subtype inclusion of the measurable
set `{ g | g.det ≠ 0 }`. -/
lemma measurableEmbedding_gToCoord :
    MeasurableEmbedding (gToCoord (n := n)) :=
  (matrixToCoordMeasEquiv (n := n)).measurableEmbedding.comp
    (MeasurableEmbedding.subtype_coe measurableSet_det_ne_zero)

/-- `gToCoord` is measurable. -/
lemma measurable_gToCoord : Measurable (gToCoord (n := n)) :=
  measurableEmbedding_gToCoord.measurable

/-- `gToCoord` is injective. -/
lemma gToCoord_injective : Function.Injective (gToCoord (n := n)) :=
  measurableEmbedding_gToCoord.injective

#print axioms matrixToCoordMeasEquiv
#print axioms measurableEmbedding_gToCoord

/-- Chart intertwiner core: left multiplication by `g` on matrices commutes
with `leftMulCoord g` through `matrixToCoord`. -/
lemma leftMulCoord_matrixToCoord (g M : Matrix (Fin n) (Fin n) ℝ) :
    leftMulCoord g (matrixToCoord M) = matrixToCoord (g * M) := by
  rw [leftMulCoord, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]; rfl

/-- Chart intertwiner core for right multiplication. -/
lemma rightMulCoord_matrixToCoord (g M : Matrix (Fin n) (Fin n) ℝ) :
    rightMulCoord g (matrixToCoord M) = matrixToCoord (M * g) := by
  rw [rightMulCoord, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]; rfl

/-- **Left intertwiner.** `gToCoord` carries left multiplication by `g₀` on
`G n` to `leftMulCoord g₀.1` on the coordinate space. -/
lemma gToCoord_leftMul (g₀ g : G n) :
    gToCoord (g₀ * g) = leftMulCoord g₀.1 (gToCoord g) := by
  simp only [gToCoord, leftMulCoord_matrixToCoord, G_coe_mul]

/-- **Right intertwiner.** `gToCoord` carries right multiplication by `g₀` on
`G n` to `rightMulCoord g₀.1` on the coordinate space. -/
lemma gToCoord_rightMul (g₀ g : G n) :
    gToCoord (g * g₀) = rightMulCoord g₀.1 (gToCoord g) := by
  simp only [gToCoord, rightMulCoord_matrixToCoord, G_coe_mul]

#print axioms gToCoord_leftMul
#print axioms gToCoord_rightMul

/-! ### GL_n Haar: the measure `nuG` on `G n` and its bi invariance

`nuG` is `haarGCoord` pulled back to `G n` along the chart `gToCoord`. The
range of `gToCoord` is the invertible locus `{ w | (matrixToCoord.symm w).det ≠ 0 }`,
which is preserved by `leftMulCoord g₀.1` and `rightMulCoord g₀.1` (multiplying
by an invertible matrix scales the determinant by `det g₀ ≠ 0`). Combined with
the bi invariance of `haarGCoord`, this makes `nuG` both left and right
invariant on `G n`. -/

/-- The pullback of the explicit `GL_n` Haar measure to `G n` along the
chart `gToCoord`. -/
noncomputable def nuG : Measure (G n) := Measure.comap gToCoord haarGCoord

/-- The range of the chart is exactly the invertible locus in coordinates. -/
lemma range_gToCoord :
    Set.range (gToCoord (n := n)) = {w | (matrixToCoord.symm w).det ≠ 0} := by
  ext w
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, rfl⟩
    show (matrixToCoord.symm (matrixToCoord g.1)).det ≠ 0
    rw [LinearEquiv.symm_apply_apply]; exact g.2
  · intro hw
    exact ⟨⟨matrixToCoord.symm w, hw⟩, matrixToCoord.apply_symm_apply w⟩

/-- The range of `gToCoord` is measurable. -/
lemma measurableSet_range_gToCoord :
    MeasurableSet (Set.range (gToCoord (n := n))) :=
  measurableEmbedding_gToCoord.measurableSet_range

/-- Pushing `nuG` forward along the chart recovers `haarGCoord` restricted to
the chart range. -/
lemma map_gToCoord_nuG :
    Measure.map gToCoord (nuG (n := n))
      = haarGCoord.restrict (Set.range (gToCoord (n := n))) := by
  unfold nuG
  exact measurableEmbedding_gToCoord.map_comap haarGCoord

/-- `leftMulCoord g₀.1` preserves the chart range. -/
lemma leftMulCoord_preimage_range_gToCoord (g₀ : G n) :
    (leftMulCoord g₀.1) ⁻¹' (Set.range (gToCoord (n := n)))
      = Set.range (gToCoord (n := n)) := by
  rw [range_gToCoord]
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hsymm : matrixToCoord.symm (leftMulCoord g₀.1 w) = g₀.1 * matrixToCoord.symm w := by
    rw [leftMulCoord, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]; rfl
  rw [hsymm, Matrix.det_mul]
  exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero g₀.2 h⟩

/-- `rightMulCoord g₀.1` preserves the chart range. -/
lemma rightMulCoord_preimage_range_gToCoord (g₀ : G n) :
    (rightMulCoord g₀.1) ⁻¹' (Set.range (gToCoord (n := n)))
      = Set.range (gToCoord (n := n)) := by
  rw [range_gToCoord]
  ext w
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hsymm : matrixToCoord.symm (rightMulCoord g₀.1 w) = matrixToCoord.symm w * g₀.1 := by
    rw [rightMulCoord, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]; rfl
  rw [hsymm, Matrix.det_mul]
  exact ⟨fun h => left_ne_zero_of_mul h, fun h => mul_ne_zero h g₀.2⟩

/-- A measurable, `haarGCoord` preserving, range preserving self map of the
coordinate space also preserves `haarGCoord` restricted to the chart range. -/
lemma map_restrict_range_gToCoord_of_invariant
    {f : ((Fin n × Fin n) → ℝ) → ((Fin n × Fin n) → ℝ)} (hf : Measurable f)
    (hmap : Measure.map f haarGCoord = haarGCoord)
    (hrange : f ⁻¹' (Set.range (gToCoord (n := n))) = Set.range (gToCoord (n := n))) :
    Measure.map f (haarGCoord.restrict (Set.range (gToCoord (n := n))))
      = haarGCoord.restrict (Set.range (gToCoord (n := n))) := by
  refine Measure.ext fun T hT => ?_
  have hpre : MeasurableSet (f ⁻¹' T) := hf hT
  rw [Measure.map_apply hf hT, Measure.restrict_apply hpre, Measure.restrict_apply hT,
    show f ⁻¹' T ∩ Set.range (gToCoord (n := n))
        = f ⁻¹' (T ∩ Set.range (gToCoord (n := n))) by rw [Set.preimage_inter, hrange],
    ← Measure.map_apply hf (hT.inter measurableSet_range_gToCoord), hmap]

/-- **Left invariance of `nuG`.** -/
lemma map_leftMul_nuG (g₀ : G n) :
    Measure.map (fun g : G n => g₀ * g) (nuG (n := n)) = nuG := by
  have hL : Measurable (fun g : G n => g₀ * g) :=
    (continuous_const.mul continuous_id).measurable
  have hLC : Measurable (leftMulCoord g₀.1) :=
    (leftMulCoord g₀.1).continuous_of_finiteDimensional.measurable
  have hcomp : gToCoord ∘ (fun g : G n => g₀ * g) = (leftMulCoord g₀.1) ∘ gToCoord := by
    funext g; exact gToCoord_leftMul g₀ g
  have key : Measure.map gToCoord (Measure.map (fun g : G n => g₀ * g) (nuG (n := n)))
      = Measure.map gToCoord (nuG (n := n)) := by
    rw [Measure.map_map measurable_gToCoord hL, hcomp,
      ← Measure.map_map hLC measurable_gToCoord, map_gToCoord_nuG,
      map_restrict_range_gToCoord_of_invariant hLC
        (map_leftMulCoord_haarGCoord g₀.1 g₀.2)
        (leftMulCoord_preimage_range_gToCoord g₀)]
  calc Measure.map (fun g : G n => g₀ * g) (nuG (n := n))
      = Measure.comap gToCoord
          (Measure.map gToCoord (Measure.map (fun g : G n => g₀ * g) (nuG (n := n)))) :=
        (measurableEmbedding_gToCoord.comap_map _).symm
    _ = Measure.comap gToCoord (Measure.map gToCoord (nuG (n := n))) := by rw [key]
    _ = nuG := measurableEmbedding_gToCoord.comap_map (nuG (n := n))

/-- **Right invariance of `nuG`.** -/
lemma map_rightMul_nuG (g₀ : G n) :
    Measure.map (fun g : G n => g * g₀) (nuG (n := n)) = nuG := by
  have hR : Measurable (fun g : G n => g * g₀) :=
    (continuous_id.mul continuous_const).measurable
  have hRC : Measurable (rightMulCoord g₀.1) :=
    (rightMulCoord g₀.1).continuous_of_finiteDimensional.measurable
  have hcomp : gToCoord ∘ (fun g : G n => g * g₀) = (rightMulCoord g₀.1) ∘ gToCoord := by
    funext g; exact gToCoord_rightMul g₀ g
  have key : Measure.map gToCoord (Measure.map (fun g : G n => g * g₀) (nuG (n := n)))
      = Measure.map gToCoord (nuG (n := n)) := by
    rw [Measure.map_map measurable_gToCoord hR, hcomp,
      ← Measure.map_map hRC measurable_gToCoord, map_gToCoord_nuG,
      map_restrict_range_gToCoord_of_invariant hRC
        (map_rightMulCoord_haarGCoord g₀.1 g₀.2)
        (rightMulCoord_preimage_range_gToCoord g₀)]
  calc Measure.map (fun g : G n => g * g₀) (nuG (n := n))
      = Measure.comap gToCoord
          (Measure.map gToCoord (Measure.map (fun g : G n => g * g₀) (nuG (n := n)))) :=
        (measurableEmbedding_gToCoord.comap_map _).symm
    _ = Measure.comap gToCoord (Measure.map gToCoord (nuG (n := n))) := by rw [key]
    _ = nuG := measurableEmbedding_gToCoord.comap_map (nuG (n := n))

#print axioms nuG
#print axioms map_leftMul_nuG
#print axioms map_rightMul_nuG

/-! ### GL_n Haar: `nuG` is a Haar measure on `G n`

The chart `gToCoord` is continuous and an open embedding (all norm free, using
`continuous_of_finiteDimensional` and the existing open embedding
`G_isOpenEmbedding`). With left invariance already established, `nuG` is finite
on compacts (a compact in `G n` maps to a compact in the invertible locus where
the density `|det|^(-n)` is bounded) and positive on opens (the density is
strictly positive on the invertible locus), hence a Haar measure. -/

/-- `matrixToCoord` is continuous (a linear map between finite dimensional real
spaces; no norm on the matrix space is needed). -/
lemma continuous_matrixToCoord : Continuous (matrixToCoord (n := n)) :=
  matrixToCoord.toLinearMap.continuous_of_finiteDimensional

/-- `matrixToCoord.symm` is continuous. -/
lemma continuous_matrixToCoord_symm : Continuous (matrixToCoord (n := n)).symm :=
  matrixToCoord.symm.toLinearMap.continuous_of_finiteDimensional

/-- `matrixToCoord` is an open map (its inverse is continuous). -/
lemma isOpenMap_matrixToCoord : IsOpenMap (matrixToCoord (n := n)) := by
  intro U hU
  have hset : matrixToCoord (n := n) '' U = (matrixToCoord (n := n)).symm ⁻¹' U := by
    ext w
    constructor
    · rintro ⟨M, hM, rfl⟩
      rw [Set.mem_preimage, LinearEquiv.symm_apply_apply]; exact hM
    · intro hw
      exact ⟨matrixToCoord.symm w, hw, matrixToCoord.apply_symm_apply w⟩
  rw [hset]
  exact hU.preimage continuous_matrixToCoord_symm

/-- `gToCoord` is continuous. -/
lemma continuous_gToCoord : Continuous (gToCoord (n := n)) :=
  continuous_matrixToCoord.comp continuous_subtype_val

/-- `gToCoord` is an open map (composite of the open map `matrixToCoord` and the
open embedding `Subtype.val`). -/
lemma isOpenMap_gToCoord : IsOpenMap (gToCoord (n := n)) :=
  isOpenMap_matrixToCoord.comp G_isOpenEmbedding.isOpenMap

/-- `nuG` is left invariant (from `map_leftMul_nuG`). -/
instance instIsMulLeftInvariant_nuG : (nuG (n := n)).IsMulLeftInvariant :=
  ⟨map_leftMul_nuG⟩

/-- The density `detWeightCoord` is nonzero on the invertible locus. -/
lemma detWeightCoord_ne_zero_of_det_ne_zero {w : (Fin n × Fin n) → ℝ}
    (hw : (matrixToCoord.symm w).det ≠ 0) : detWeightCoord w ≠ 0 := by
  unfold detWeightCoord
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, inv_pos]
  exact pow_pos (abs_pos.mpr hw) n

/-- `nuG` is finite on compact sets: a compact subset of `G n` maps to a compact
subset of the invertible locus, where the continuous density `|det|^(-n)` is
bounded; the chart image has finite Lebesgue measure. -/
instance instIsFiniteMeasureOnCompacts_nuG : IsFiniteMeasureOnCompacts (nuG (n := n)) := by
  refine ⟨fun K hK => ?_⟩
  rw [show nuG (n := n) K = haarGCoord (gToCoord '' K) from
        measurableEmbedding_gToCoord.comap_apply haarGCoord K]
  have hCcomp : IsCompact (gToCoord (n := n) '' K) := hK.image continuous_gToCoord
  have hCmeas : MeasurableSet (gToCoord (n := n) '' K) :=
    measurableEmbedding_gToCoord.measurableSet_image' hK.measurableSet
  have hCsub : ∀ w ∈ gToCoord (n := n) '' K, (matrixToCoord.symm w).det ≠ 0 := by
    intro w hw
    have hwr : w ∈ Set.range (gToCoord (n := n)) := Set.image_subset_range _ _ hw
    rwa [range_gToCoord] at hwr
  have hcontOn : ContinuousOn (fun w => (|(matrixToCoord.symm w).det| ^ n)⁻¹)
      (gToCoord (n := n) '' K) :=
    ((continuous_abs.comp continuous_det_matrixToCoord_symm).pow n).continuousOn.inv₀
      (fun w hw => pow_ne_zero n (abs_ne_zero.mpr (hCsub w hw)))
  obtain ⟨B, hB⟩ := hCcomp.exists_bound_of_continuousOn hcontOn
  unfold haarGCoord
  rw [withDensity_apply _ hCmeas]
  calc ∫⁻ w in gToCoord (n := n) '' K, detWeightCoord w ∂volume
      ≤ ∫⁻ _ in gToCoord (n := n) '' K, ENNReal.ofReal B ∂volume := by
        refine setLIntegral_mono measurable_const (fun w hw => ?_)
        show ENNReal.ofReal ((|(matrixToCoord.symm w).det| ^ n)⁻¹) ≤ ENNReal.ofReal B
        exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hB w hw))
    _ = ENNReal.ofReal B * volume (gToCoord (n := n) '' K) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCcomp.measure_lt_top

/-- `nuG` is positive on nonempty open sets: the chart maps an open set to an
open subset of the invertible locus, where the density is strictly positive. -/
instance instIsOpenPosMeasure_nuG : (nuG (n := n)).IsOpenPosMeasure := by
  refine ⟨fun U hU hUne => ?_⟩
  rw [show nuG (n := n) U = haarGCoord (gToCoord '' U) from
        measurableEmbedding_gToCoord.comap_apply haarGCoord U]
  have hVopen : IsOpen (gToCoord (n := n) '' U) := isOpenMap_gToCoord U hU
  have hVne : (gToCoord (n := n) '' U).Nonempty := hUne.image _
  have hVsub : gToCoord (n := n) '' U ⊆ Function.support (detWeightCoord (n := n)) := by
    intro w hw
    have hwr : w ∈ Set.range (gToCoord (n := n)) := Set.image_subset_range _ _ hw
    rw [range_gToCoord] at hwr
    exact Function.mem_support.mpr (detWeightCoord_ne_zero_of_det_ne_zero hwr)
  unfold haarGCoord
  rw [withDensity_apply _ hVopen.measurableSet]
  have hpos : 0 < ∫⁻ w in gToCoord (n := n) '' U, detWeightCoord w ∂volume := by
    rw [setLIntegral_pos_iff measurable_detWeightCoord, Set.inter_eq_right.mpr hVsub]
    exact IsOpen.measure_pos volume hVopen hVne
  exact hpos.ne'

/-- **`nuG` is a Haar measure on `G n`** (left invariant, finite on compacts,
positive on opens). -/
instance instIsHaarMeasure_nuG : (nuG (n := n)).IsHaarMeasure := ⟨⟩

#print axioms isOpenMap_gToCoord
#print axioms instIsFiniteMeasureOnCompacts_nuG
#print axioms instIsOpenPosMeasure_nuG
#print axioms instIsHaarMeasure_nuG

/-! ### GL_n is unimodular: the modular character is trivial

Since `nuG` is a Haar measure on `G n` that is also right invariant
(`map_rightMul_nuG`), and the modular character does not depend on the chosen
Haar measure (`modularCharacterFun_eq_haarScalarFactor`), its scalar factor is
`haarScalarFactor nuG nuG = 1`. This is the measure level statement of
unimodularity of `GL_n(ℝ)`. -/

/-- **Unimodularity of `GL_n(ℝ)`.** The modular character of `G n` is trivial:
`modularCharacterFun g = 1` for every `g : G n`. Computed with the explicit bi
invariant Haar measure `nuG`: right invariance makes the Haar scalar factor of
right translation equal to `haarScalarFactor nuG nuG = 1`. -/
theorem modularCharacterFun_eq_one (g : G n) :
    Measure.modularCharacterFun g = 1 := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (nuG (n := n)) g]
  simp only [map_rightMul_nuG]
  exact Measure.haarScalarFactor_self _

#print axioms modularCharacterFun_eq_one

/-! ### Regularity of `nuG` and identification with `haarG`

`G n` is second countable (it embeds openly into the second countable matrix
space) and pseudo metrizable, hence sigma compact (it is also locally compact).
A locally finite measure on such a space is regular and inner regular, so both
`nuG` and `haarG` are inner regular. Haar uniqueness then identifies `nuG` with
`haarG` up to a positive scalar. -/

/-- `G n` is second countable, transported from the second countable matrix
space through the open embedding `Subtype.val`. -/
instance instSecondCountableG : SecondCountableTopology (G n) :=
  G_isOpenEmbedding.isEmbedding.secondCountableTopology

/-- `G n` is pseudo metrizable, transported from the matrix space through the
inducing map `Subtype.val`. -/
instance instPseudoMetrizableG : TopologicalSpace.PseudoMetrizableSpace (G n) :=
  G_isOpenEmbedding.isEmbedding.toIsInducing.pseudoMetrizableSpace

/-- `nuG` is regular: a locally finite measure on the sigma compact, pseudo
metrizable group `G n`. -/
instance instRegular_nuG : (nuG (n := n)).Regular := inferInstance

/-- **Identification of `nuG` with the abstract Haar measure.** By Haar
uniqueness, the explicit pullback `nuG` of `haarGCoord` equals the project's
canonical Haar measure `haarG` up to the positive scalar
`haarScalarFactor nuG haarG`. -/
lemma nuG_eq_haarScalarFactor_smul_haarG :
    nuG (n := n) = Measure.haarScalarFactor (nuG (n := n)) haarG • haarG :=
  Measure.isMulLeftInvariant_eq_smul_of_innerRegular nuG haarG

#print axioms instRegular_nuG
#print axioms nuG_eq_haarScalarFactor_smul_haarG

/-! ### Level 0: factor Haar identifications for `A` and `U`

Mirroring `nuG = c . haarG`. `nuU` already carries its regularity instances, so the
`U` identification is immediate. For `A`, `haarAExplicit` only needs the finite on
compacts and regular instances (transported through the log chart homeomorphism, like
`nuU`); inner regularity then follows on the second countable, pseudo metrizable,
sigma compact group `A n`. Haar uniqueness then identifies each with the canonical
factor Haar up to a positive scalar. -/

/-- `haarAExplicit` is finite on compacts (pushforward of `volume` via the log
chart homeomorphism). -/
instance instIsFiniteOnCompacts_haarAExplicit :
    IsFiniteMeasureOnCompacts (haarAExplicit (n := n)) := by
  refine ⟨fun K hK => ?_⟩
  have hpre : (A.toFinNRHomeomorph (n := n)).symm ⁻¹' K
      = (A.toFinNRHomeomorph (n := n)) '' K := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      exact ⟨(A.toFinNRHomeomorph (n := n)).symm v, h,
        (A.toFinNRHomeomorph (n := n)).apply_symm_apply v⟩
    · rintro ⟨D, hD, rfl⟩
      rwa [Homeomorph.symm_apply_apply]
  unfold haarAExplicit
  rw [Measure.map_apply (A.toFinNRHomeomorph (n := n)).symm.measurable hK.measurableSet, hpre]
  exact (hK.image (A.toFinNRHomeomorph (n := n)).continuous).measure_lt_top

/-- `haarAExplicit` is regular (pushforward of the regular `volume`). -/
instance instRegular_haarAExplicit : (haarAExplicit (n := n)).Regular :=
  Measure.Regular.map (A.toFinNRHomeomorph (n := n)).symm

/-- **A factor identification.** `haarAExplicit` equals `haarA` up to a positive
scalar, by Haar uniqueness. -/
lemma haarAExplicit_eq_haarScalarFactor_smul_haarA :
    haarAExplicit (n := n)
      = Measure.haarScalarFactor (haarAExplicit (n := n)) haarA • haarA :=
  Measure.isMulLeftInvariant_eq_smul_of_innerRegular haarAExplicit haarA

/-- **U factor identification.** `nuU` equals `haarN` up to a positive scalar, by
Haar uniqueness. -/
lemma nuU_eq_haarScalarFactor_smul_haarN :
    nuU (n := n) = Measure.haarScalarFactor (nuU (n := n)) haarN • haarN :=
  Measure.isMulLeftInvariant_eq_smul_of_innerRegular nuU haarN

#print axioms haarAExplicit_eq_haarScalarFactor_smul_haarA
#print axioms nuU_eq_haarScalarFactor_smul_haarN

end Complete
end IwasawaCoC

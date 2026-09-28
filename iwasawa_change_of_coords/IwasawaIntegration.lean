/-
# The Iwasawa integration formula for `GL_n(ℝ)`

This file proves the measure theoretic statement the rest of the project builds
toward: Haar measure on `G = GL_n(ℝ)`, written in Iwasawa coordinates
`g = k · a · u`, is the product of the Haar measures on `K = O(n)`, `A` and `U`,
weighted by the Iwasawa character

  `δ(a) = ∏_{i<j} aᵢ / aⱼ = det (Ad(a) on 𝔫)`.

## Main results

* `map_iwasawaMap_haar`: for some constant `c > 0`,
  `map iwasawaMap (haarK × (δ · haarA) × haarN) = c • haarG`.
* `lintegral_iwasawa`: the same statement as an integration formula,
  `c · ∫ f dg = ∫_K ∫_A δ(a) ∫_U f(k a u) du da dk` for measurable `f ≥ 0`.
* `map_iwasawaMapJL_haar`: the Jorgenson-Lang ordering `g = u · a · k`, where the
  weight becomes `δ(a)⁻¹`.
* Along the way: `U` is unimodular (`modularCharacterFun_UU_eq_one`), `K` is
  unimodular (`modularCharacterFun_K_eq_one`), and a unimodular Haar measure is
  invariant under inversion (`isInvInvariant_of_isMulRightInvariant`).

## Proof

The classical Haar uniqueness argument (Knapp, *Lie Groups Beyond an
Introduction*, 2nd ed., Prop. 8.43; Folland, *A Course in Abstract Harmonic
Analysis*, 2nd ed., Thm. 2.51). No Jacobian and no chart on `K` is needed.

1. `B = A · U` (upper triangular, positive diagonal) is a subgroup of `G`, and
   `(a, u) ↦ a · u` is a homeomorphism `A × U ≃ₜ B` (`toBBHomeomorph`).
2. `(k, b) ↦ k · b⁻¹` is a homeomorphism `K × B ≃ₜ G` (`kbHomeomorph`) that turns
   left multiplication by `(k₀, b₀)` on the product group `K × B` into
   `g ↦ k₀ g b₀⁻¹` on `G`. Because `GL_n(ℝ)` is unimodular
   (`modularCharacterFun_eq_one`), `haarG` is invariant under that map, so its
   pullback `haarKB` is a left Haar measure on `K × B`.
3. The candidate `haarK × (δ · haarA) × haarN`, moved to `K × B` by
   `(k, a, u) ↦ (k, (a u)⁻¹)`, is also left invariant. On the `B` factor this
   is the identity `(a u)(a' u') = (a a') ((a'⁻¹ u a') u')`: translating the `A`
   coordinate rescales `δ · haarA` by `δ(a')⁻¹`, and conjugating then translating
   the `U` coordinate rescales `haarN` by `δ(a')` (`map_conjAut_haarN` together
   with the unimodularity of `U`). The two factors cancel.
4. Haar uniqueness on the second countable group `K × B` identifies the two
   measures up to a constant, and pushing forward along `kbHomeomorph` gives the
   formula on `G`.
-/

import iwasawa_change_of_coords.IwasawaHaar

namespace IwasawaCoC
namespace Complete

open MeasureTheory Measure Matrix Iwasawa
open scoped ENNReal NNReal

variable {n : ℕ}

/-! ## Small facts about `A n` -/

lemma A_val_mul_inv (a : A n) : a.1 * a.1⁻¹ = 1 :=
  Matrix.mul_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')

lemma A_val_inv_mul (a : A n) : a.1⁻¹ * a.1 = 1 :=
  Matrix.nonsing_inv_mul a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')

lemma A_val_inv_inv (a : A n) : (a.1⁻¹)⁻¹ = a.1 :=
  Matrix.nonsing_inv_nonsing_inv a.1 (isUnit_iff_ne_zero.mpr a.2.det_pos.ne')

/-- Diagonal entries of a product of positive diagonal matrices multiply. -/
lemma A_mul_apply_self (a b : A n) (i : Fin n) :
    (a * b).1 i i = a.1 i i * b.1 i i := by
  show (a.1 * b.1) i i = a.1 i i * b.1 i i
  rw [Matrix.mul_apply, Finset.sum_eq_single i
    (fun k _ hk => by rw [a.2.1 i k (Ne.symm hk), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)]

/-! ## The Iwasawa character `δ` -/

/-- The Iwasawa character `δ(a) = ∏_{i<j} aᵢᵢ / aⱼⱼ`. It is the determinant of
`Ad(a) : X ↦ a X a⁻¹` on the strictly upper triangular matrices
(`iwasawaDelta_eq_det_adNN`), and `e^{2ρ}` in Lie theoretic notation. -/
noncomputable def iwasawaDelta (a : A n) : ℝ :=
  ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2

lemma iwasawaDelta_eq_det_adNN (a : A n) :
    iwasawaDelta a = LinearMap.det (adNN a).toLinearMap :=
  (adNN_det_eq_pair_product a).symm

lemma iwasawaDelta_pos (a : A n) : 0 < iwasawaDelta a :=
  Finset.prod_pos fun ij _ => div_pos (a.2.2 ij.1.1) (a.2.2 ij.1.2)

lemma iwasawaDelta_mul (a b : A n) :
    iwasawaDelta (a * b) = iwasawaDelta a * iwasawaDelta b := by
  unfold iwasawaDelta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ => ?_
  rw [A_mul_apply_self, A_mul_apply_self, mul_div_mul_comm]

lemma iwasawaDelta_one : iwasawaDelta (1 : A n) = 1 := by
  unfold iwasawaDelta
  refine Finset.prod_eq_one fun ij _ => ?_
  show (1 : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.1
      / (1 : Matrix (Fin n) (Fin n) ℝ) ij.1.2 ij.1.2 = 1
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, div_one]

lemma iwasawaDelta_inv (a : A n) : iwasawaDelta a⁻¹ = (iwasawaDelta a)⁻¹ := by
  have h := iwasawaDelta_mul a a⁻¹
  rw [mul_inv_cancel, iwasawaDelta_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma continuous_iwasawaDelta : Continuous (iwasawaDelta (n := n)) := by
  unfold iwasawaDelta
  refine continuous_finset_prod _ fun ij _ => ?_
  have hent : ∀ i : Fin n, Continuous fun a : A n => a.1 i i := fun i =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (hent _).div (hent _) fun a => (a.2.2 ij.1.2).ne'

/-- `δ` as a nonnegative real, the form used as a density. -/
noncomputable def iwasawaDeltaNN (a : A n) : ℝ≥0 :=
  ⟨iwasawaDelta a, (iwasawaDelta_pos a).le⟩

@[simp] lemma coe_iwasawaDeltaNN (a : A n) : (iwasawaDeltaNN a : ℝ) = iwasawaDelta a := rfl

lemma iwasawaDeltaNN_ne_zero (a : A n) : iwasawaDeltaNN a ≠ 0 := by
  rw [← NNReal.coe_ne_zero, coe_iwasawaDeltaNN]
  exact (iwasawaDelta_pos a).ne'

lemma iwasawaDeltaNN_mul (a b : A n) :
    iwasawaDeltaNN (a * b) = iwasawaDeltaNN a * iwasawaDeltaNN b :=
  NNReal.eq (by rw [NNReal.coe_mul, coe_iwasawaDeltaNN, coe_iwasawaDeltaNN,
    coe_iwasawaDeltaNN, iwasawaDelta_mul])

lemma iwasawaDeltaNN_inv (a : A n) : iwasawaDeltaNN a⁻¹ = (iwasawaDeltaNN a)⁻¹ :=
  NNReal.eq (by rw [NNReal.coe_inv, coe_iwasawaDeltaNN, coe_iwasawaDeltaNN,
    iwasawaDelta_inv])

lemma continuous_iwasawaDeltaNN : Continuous (iwasawaDeltaNN (n := n)) :=
  continuous_iwasawaDelta.subtype_mk _

lemma measurable_iwasawaDeltaNN : Measurable (iwasawaDeltaNN (n := n)) :=
  continuous_iwasawaDeltaNN.measurable

lemma measurable_iwasawaDeltaENN :
    Measurable fun a : A n => (iwasawaDeltaNN a : ℝ≥0∞) :=
  measurable_iwasawaDeltaNN.coe_nnreal_ennreal

/-! ## `U` is unimodular

Right translation in the strict upper entry chart is affine with unipotent
linear part, exactly as for left translation (`instIsMulLeftInvariant_nuU`). -/

/-- Right multiplication by a strictly upper triangular `Y`, as an
endomorphism of `NN n`. -/
def rightMulNN (Y : NN n) : NN n →ₗ[ℝ] NN n where
  toFun X := ⟨X.1 * Y.1, nn_mul_mem X Y⟩
  map_add' X X' := by
    apply Subtype.ext
    show (X + X' : NN n).1 * Y.1 = X.1 * Y.1 + X'.1 * Y.1
    rw [Submodule.coe_add, Matrix.add_mul]
  map_smul' c X := by
    apply Subtype.ext
    show (c • X : NN n).1 * Y.1 = c • (X.1 * Y.1)
    rw [SetLike.val_smul, Matrix.smul_mul]

@[simp] lemma rightMulNN_apply_val (Y X : NN n) :
    ((rightMulNN Y X : NN n) : Matrix (Fin n) (Fin n) ℝ) = X.1 * Y.1 := rfl

lemma rightMulNN_pow_apply_val (Y : NN n) (m : ℕ) (X : NN n) :
    (((rightMulNN Y) ^ m) X : Matrix (Fin n) (Fin n) ℝ) = X.1 * Y.1 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, rightMulNN_apply_val, ih, pow_succ,
      Matrix.mul_assoc]

lemma rightMulNN_isNilpotent (Y : NN n) : IsNilpotent (rightMulNN Y) := by
  obtain ⟨m, hm⟩ := nn_isNilpotent Y
  refine ⟨m, LinearMap.ext fun X => Subtype.ext ?_⟩
  show (((rightMulNN Y) ^ m) X : Matrix (Fin n) (Fin n) ℝ)
      = ((0 : NN n →ₗ[ℝ] NN n) X : NN n)
  rw [rightMulNN_pow_apply_val, hm, Matrix.mul_zero]
  rfl

/-- The linear part of right translation in chart coordinates. -/
noncomputable def transLinR (Y : NN n) : (nnIndex n → ℝ) →ₗ[ℝ] (nnIndex n → ℝ) :=
  nnCoordEquiv.toLinearMap ∘ₗ ((1 : Module.End ℝ (NN n)) + rightMulNN Y) ∘ₗ
      nnCoordEquiv.symm.toLinearMap

lemma det_transLinR (Y : NN n) : LinearMap.det (transLinR Y) = 1 := by
  rw [transLinR, LinearMap.det_conj]
  exact det_one_add_of_isNilpotent (rightMulNN_isNilpotent Y)

lemma transLinR_apply (Y : NN n) (w : nnIndex n → ℝ) (ij : nnIndex n) :
    transLinR Y w ij = w ij + (coordMat w * Y.1) ij.1.1 ij.1.2 := by
  have h1 : transLinR Y w
      = nnCoordEquiv (nnCoordEquiv.symm w + rightMulNN Y (nnCoordEquiv.symm w)) := by
    simp only [transLinR, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply,
      Module.End.one_apply]
  rw [h1, map_add, Pi.add_apply, nnCoordEquiv_apply, nnCoordEquiv_apply,
    rightMulNN_apply_val, nnCoordEquiv_symm_val]
  congr 1
  show coordMat w ij.1.1 ij.1.2 = w ij
  simp only [coordMat]; exact dif_pos ij.2

lemma fromCoords_mul_u (u₀ : UU n) (w : nnIndex n → ℝ) :
    fromCoords w * u₀.1 = coordMat w * (u₀.1 - 1) + coordMat w + u₀.1 := by
  rw [fromCoords_eq]; noncomm_ring

/-- Right multiplication by `u₀`, read in the chart, is the affine map
`w ↦ transLinR (u₀ - 1) w + nnChart u₀`. -/
lemma rightMul_nnChart_symm (u₀ : UU n) (w : nnIndex n → ℝ) :
    nnChart.symm w * u₀
      = nnChart.symm (transLinR (UU.toNNHomeomorph u₀) w + nnChart u₀) := by
  apply nnChart.injective
  rw [Homeomorph.apply_symm_apply]
  funext ij
  have hcm : coordMat w ij.1.1 ij.1.2 = w ij := by
    simp only [coordMat]; exact dif_pos ij.2
  rw [Pi.add_apply, transLinR_apply]
  show (fromCoords w * u₀.1) ij.1.1 ij.1.2
      = (w ij + (coordMat w * (u₀.1 - 1)) ij.1.1 ij.1.2) + u₀.1 ij.1.1 ij.1.2
  rw [fromCoords_mul_u, Matrix.add_apply, Matrix.add_apply, hcm]
  ring

lemma map_transLinR_volume (Y : NN n) :
    Measure.map (transLinR Y) (volume : Measure (nnIndex n → ℝ)) = volume := by
  have hne : LinearMap.det (transLinR Y) ≠ 0 := by rw [det_transLinR]; norm_num
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, det_transLinR]
  simp

lemma map_transAffineR_volume (Y : NN n) (c : nnIndex n → ℝ) :
    Measure.map (fun w => transLinR Y w + c) (volume : Measure (nnIndex n → ℝ)) = volume := by
  have hf : (fun w => transLinR Y w + c) = (fun x => x + c) ∘ (transLinR Y) := by
    funext w; rfl
  rw [hf, ← Measure.map_map (measurable_add_const c)
      (transLinR Y).continuous_of_finiteDimensional.measurable,
    map_transLinR_volume, map_add_right_eq_self]

/-- The explicit `U` measure `nuU` is right invariant. -/
instance instIsMulRightInvariant_nuU : (nuU (n := n)).IsMulRightInvariant := by
  refine ⟨fun u₀ => ?_⟩
  have hmR : Measurable (fun u : UU n => u * u₀) :=
    (continuous_id.mul continuous_const).measurable
  have hmChart : Measurable (nnChart (n := n)).symm := (nnChart (n := n)).symm.measurable
  have hmAff : Measurable
      (fun w : nnIndex n → ℝ => transLinR (UU.toNNHomeomorph u₀) w + nnChart u₀) :=
    ((transLinR (UU.toNNHomeomorph u₀)).continuous_of_finiteDimensional.measurable).add_const _
  have hcomp : (fun u : UU n => u * u₀) ∘ (nnChart (n := n)).symm
      = (nnChart (n := n)).symm
          ∘ (fun w => transLinR (UU.toNNHomeomorph u₀) w + nnChart u₀) := by
    funext w; exact rightMul_nnChart_symm u₀ w
  unfold nuU
  rw [Measure.map_map hmR hmChart, hcomp, ← Measure.map_map hmChart hmAff,
    map_transAffineR_volume]

/-- **`U` is unimodular**: its modular character is trivial. -/
theorem modularCharacterFun_UU_eq_one (u : UU n) : Measure.modularCharacterFun u = 1 := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (nuU (n := n)) u]
  simp only [map_mul_right_eq_self]
  exact Measure.haarScalarFactor_self _

/-- `haarN` is right invariant. -/
instance instIsMulRightInvariant_haarN : (haarN (n := n)).IsMulRightInvariant :=
  ⟨fun u => by
    rw [map_right_mul_eq_modularCharacterFun_smul haarN u, modularCharacterFun_UU_eq_one,
      one_smul]⟩

/-! ## `K` and `G` are unimodular -/

instance instSecondCountableK : SecondCountableTopology (K n) :=
  inferInstanceAs
    (SecondCountableTopology ({Q : Matrix (Fin n) (Fin n) ℝ | IsOrthogonal Q} : Set _))

/-- **`K = O(n)` is unimodular**: it is compact, and the modular character of a
compact group is trivial because right translation preserves total mass. -/
theorem modularCharacterFun_K_eq_one (k : K n) : Measure.modularCharacterFun k = 1 := by
  have h := map_right_mul_eq_modularCharacterFun_smul (haarK (n := n)) k
  have hu : (Measure.map (· * k) (haarK (n := n))) Set.univ
      = (Measure.modularCharacterFun k • haarK (n := n)) Set.univ := by rw [h]
  rw [Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply] at hu
  have h0 : (haarK (n := n)) Set.univ ≠ 0 :=
    IsOpen.measure_ne_zero _ isOpen_univ Set.univ_nonempty
  have htop : (haarK (n := n)) Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have h1 : ((1 : ℝ≥0) : ℝ≥0∞) * (haarK (n := n)) Set.univ
      = (Measure.modularCharacterFun k : ℝ≥0∞) * (haarK (n := n)) Set.univ := by
    rw [ENNReal.coe_one, one_mul]; exact hu
  exact (ENNReal.coe_inj.mp ((ENNReal.mul_left_inj h0 htop).mp h1)).symm

instance instIsMulRightInvariant_haarK : (haarK (n := n)).IsMulRightInvariant :=
  ⟨fun k => by
    rw [map_right_mul_eq_modularCharacterFun_smul haarK k, modularCharacterFun_K_eq_one,
      one_smul]⟩

/-- `haarG` is right invariant: `GL_n(ℝ)` is unimodular
(`modularCharacterFun_eq_one`). -/
instance instIsMulRightInvariant_haarG : (haarG (n := n)).IsMulRightInvariant :=
  ⟨fun g => by
    rw [map_right_mul_eq_modularCharacterFun_smul haarG g, modularCharacterFun_eq_one,
      one_smul]⟩

/-- In a second countable locally compact group, a Haar measure that is also
right invariant is invariant under inversion. (Mathlib has this for abelian
groups, `IsHaarMeasure.isInvInvariant_of_regular`; the proof is the same.) -/
lemma isInvInvariant_of_isMulRightInvariant {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul,
      pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have h3 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h4 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc, h5, one_smul]

instance instIsInvInvariant_haarG : (haarG (n := n)).IsInvInvariant :=
  isInvInvariant_of_isMulRightInvariant _

instance instIsInvInvariant_haarK : (haarK (n := n)).IsInvInvariant :=
  isInvInvariant_of_isMulRightInvariant _

instance instIsInvInvariant_haarN : (haarN (n := n)).IsInvInvariant :=
  isInvInvariant_of_isMulRightInvariant _

/-! ## The group `B = A · U` -/

/-- `B = A · U`, the upper triangular matrices with positive diagonal, as a
subgroup of `G n`. -/
def BB (n : ℕ) : Subgroup (G n) where
  carrier := {g | ∃ a : A n, ∃ u : UU n, g.1 = a.1 * u.1}
  mul_mem' := by
    rintro g h ⟨a, u, hg⟩ ⟨a', u', hh⟩
    refine ⟨a * a', conjAut a' u * u', ?_⟩
    show g.1 * h.1 = (a.1 * a'.1) * ((a'.1⁻¹ * u.1 * a'.1) * u'.1)
    rw [hg, hh]
    calc a.1 * u.1 * (a'.1 * u'.1)
        = a.1 * (a'.1 * a'.1⁻¹) * u.1 * (a'.1 * u'.1) := by
          rw [A_val_mul_inv, Matrix.mul_one]
      _ = (a.1 * a'.1) * ((a'.1⁻¹ * u.1 * a'.1) * u'.1) := by noncomm_ring
  one_mem' := ⟨1, 1, (Matrix.mul_one 1).symm⟩
  inv_mem' := by
    rintro g ⟨a, u, hg⟩
    refine ⟨a⁻¹, conjAut a⁻¹ u⁻¹, ?_⟩
    show g.1⁻¹ = a.1⁻¹ * ((a.1⁻¹)⁻¹ * u.1⁻¹ * a.1⁻¹)
    rw [hg, Matrix.mul_inv_rev, A_val_inv_inv]
    calc u.1⁻¹ * a.1⁻¹ = (a.1⁻¹ * a.1) * u.1⁻¹ * a.1⁻¹ := by
          rw [A_val_inv_mul, Matrix.one_mul]
      _ = a.1⁻¹ * (a.1 * u.1⁻¹ * a.1⁻¹) := by noncomm_ring

lemma mem_BB {g : G n} : g ∈ BB n ↔ ∃ a : A n, ∃ u : UU n, g.1 = a.1 * u.1 := Iff.rfl

/-- `(a, u) ↦ a · u`, as a map `A × U → B`. -/
noncomputable def toBB (p : A n × UU n) : BB n :=
  ⟨iwasawaMap ((1 : K n), p.1, p.2), mem_BB.mpr ⟨p.1, p.2, by
    show (1 : Matrix (Fin n) (Fin n) ℝ) * p.1.1 * p.2.1 = p.1.1 * p.2.1
    rw [Matrix.one_mul]⟩⟩

@[simp] lemma toBB_val (p : A n × UU n) :
    (((toBB p : BB n) : G n) : Matrix (Fin n) (Fin n) ℝ) = p.1.1 * p.2.1 := by
  show (1 : Matrix (Fin n) (Fin n) ℝ) * p.1.1 * p.2.1 = p.1.1 * p.2.1
  rw [Matrix.one_mul]

/-- If `g = a · u`, its Iwasawa coordinates are `(1, a, u)`. -/
lemma iwasawaEquiv_symm_eq {g : G n} {a : A n} {u : UU n} (h : g.1 = a.1 * u.1) :
    iwasawaEquiv.symm g = ((1 : K n), a, u) := by
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  show g.1 = (1 : Matrix (Fin n) (Fin n) ℝ) * a.1 * u.1
  rw [Matrix.one_mul, h]

/-- `A × U ≃ₜ B`, `(a, u) ↦ a · u`. The inverse reads off the `A` and `U`
Iwasawa coordinates, so it is continuous by `continuous_iwasawaSymm`. -/
noncomputable def toBBHomeomorph : A n × UU n ≃ₜ BB n where
  toFun := toBB
  invFun b := (iwasawaEquiv.symm (b : G n)).2
  left_inv p := by
    show (iwasawaEquiv.symm (iwasawaEquiv ((1 : K n), p.1, p.2))).2 = p
    rw [Equiv.symm_apply_apply]
  right_inv b := by
    obtain ⟨a, u, h⟩ := mem_BB.mp b.2
    apply Subtype.ext; apply Subtype.ext
    rw [toBB_val]
    beta_reduce
    rw [iwasawaEquiv_symm_eq h]
    exact h.symm
  continuous_toFun :=
    (continuous_iwasawaMap.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  continuous_invFun :=
    continuous_snd.comp (continuous_iwasawaSymm.comp continuous_subtype_val)

lemma toBBHomeomorph_apply (p : A n × UU n) : toBBHomeomorph p = toBB p := rfl

/-- Multiplication in `B` in the coordinates `(a, u)`:
`(a u)(a' u') = (a a') ((a'⁻¹ u a') u')`. -/
lemma toBB_mul (p q : A n × UU n) :
    toBB p * toBB q = toBB (p.1 * q.1, conjAut q.1 p.2 * q.2) := by
  apply Subtype.ext; apply Subtype.ext
  show (toBB p : G n).1 * (toBB q : G n).1 = _
  rw [toBB_val, toBB_val, toBB_val]
  show p.1.1 * p.2.1 * (q.1.1 * q.2.1) = (p.1.1 * q.1.1) * ((q.1.1⁻¹ * p.2.1 * q.1.1) * q.2.1)
  calc p.1.1 * p.2.1 * (q.1.1 * q.2.1)
      = p.1.1 * (q.1.1 * q.1.1⁻¹) * p.2.1 * (q.1.1 * q.2.1) := by
        rw [A_val_mul_inv, Matrix.mul_one]
    _ = (p.1.1 * q.1.1) * ((q.1.1⁻¹ * p.2.1 * q.1.1) * q.2.1) := by noncomm_ring

instance instSecondCountableBB : SecondCountableTopology (BB n) :=
  inferInstanceAs (SecondCountableTopology ((BB n : Set (G n))))

instance instLocallyCompactSpaceBB : LocallyCompactSpace (BB n) :=
  (toBBHomeomorph (n := n)).locallyCompactSpace_iff.mp inferInstance

/-! ## The chart `K × B ≃ₜ G`, `(k, b) ↦ k · b⁻¹` -/

/-- `(k, b) ↦ k · b⁻¹`, a homeomorphism `K × B ≃ₜ G` built from the Iwasawa
homeomorphism. -/
noncomputable def kbHomeomorph : K n × BB n ≃ₜ G n :=
  ((Homeomorph.refl (K n)).prodCongr
      ((Homeomorph.inv (BB n)).trans toBBHomeomorph.symm)).trans
    iwasawaHomeomorph

lemma kbHomeomorph_apply (k : K n) (b : BB n) :
    kbHomeomorph (k, b) = iwasawaMap (k, toBBHomeomorph.symm b⁻¹) := rfl

lemma kbHomeomorph_val (k : K n) (b : BB n) :
    ((kbHomeomorph (k, b) : G n) : Matrix (Fin n) (Fin n) ℝ)
      = k.1 * (((b⁻¹ : BB n) : G n) : Matrix (Fin n) (Fin n) ℝ) := by
  set p := toBBHomeomorph.symm (b⁻¹ : BB n) with hp
  have hb : toBB p = b⁻¹ := toBBHomeomorph.apply_symm_apply _
  have hval : (((b⁻¹ : BB n) : G n) : Matrix (Fin n) (Fin n) ℝ) = p.1.1 * p.2.1 := by
    rw [← hb, toBB_val]
  rw [kbHomeomorph_apply, hval, ← Matrix.mul_assoc]
  rfl

/-- `kbHomeomorph` intertwines left multiplication on `K × B` with
`g ↦ k₀ g b₀⁻¹` on `G`. -/
lemma kbHomeomorph_mul (h x : K n × BB n) :
    kbHomeomorph (h * x) = K.toG h.1 * kbHomeomorph x * ((h.2 : G n))⁻¹ := by
  obtain ⟨k', b'⟩ := h
  obtain ⟨k, b⟩ := x
  apply Subtype.ext
  show ((kbHomeomorph (k' * k, b' * b) : G n) : Matrix (Fin n) (Fin n) ℝ)
    = k'.1 * ((kbHomeomorph (k, b) : G n) : Matrix (Fin n) (Fin n) ℝ)
      * (((b' : G n) : Matrix (Fin n) (Fin n) ℝ))⁻¹
  rw [kbHomeomorph_val, kbHomeomorph_val]
  show k'.1 * k.1 * (((b' : G n) : Matrix (Fin n) (Fin n) ℝ)
      * ((b : G n) : Matrix (Fin n) (Fin n) ℝ))⁻¹
    = k'.1 * (k.1 * (((b : G n) : Matrix (Fin n) (Fin n) ℝ))⁻¹)
      * (((b' : G n) : Matrix (Fin n) (Fin n) ℝ))⁻¹
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/-! ## `haarG` pulled back to `K × B` is a Haar measure -/

/-- `haarG` pulled back to `K × B` along `kbHomeomorph`. -/
noncomputable def haarKB : Measure (K n × BB n) := Measure.map kbHomeomorph.symm haarG

lemma map_mul_left_mul_right_haarG (c d : G n) :
    Measure.map (fun g => c * g * d) (haarG (n := n)) = haarG := by
  have hsplit : (fun g : G n => c * g * d) = (fun g => g * d) ∘ (fun g => c * g) := rfl
  rw [hsplit, ← Measure.map_map (measurable_mul_const d) (measurable_const_mul c),
    map_mul_left_eq_self, map_mul_right_eq_self]

instance instIsMulLeftInvariant_haarKB : (haarKB (n := n)).IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  have hcomm : (fun x => h * x) ∘ (kbHomeomorph (n := n)).symm
      = kbHomeomorph.symm ∘ (fun g : G n => K.toG h.1 * g * ((h.2 : G n))⁻¹) := by
    funext g
    simp only [Function.comp_apply]
    apply kbHomeomorph.injective
    rw [kbHomeomorph_mul, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  unfold haarKB
  rw [Measure.map_map (measurable_const_mul h) kbHomeomorph.symm.measurable, hcomm,
    ← Measure.map_map kbHomeomorph.symm.measurable
      ((measurable_const_mul _).mul_const _), map_mul_left_mul_right_haarG]

instance instIsFiniteMeasureOnCompacts_haarKB :
    IsFiniteMeasureOnCompacts (haarKB (n := n)) :=
  IsFiniteMeasureOnCompacts.map haarG kbHomeomorph.symm

instance instIsOpenPosMeasure_haarKB : (haarKB (n := n)).IsOpenPosMeasure :=
  kbHomeomorph.symm.continuous.isOpenPosMeasure_map kbHomeomorph.symm.surjective

instance instIsHaarMeasure_haarKB : (haarKB (n := n)).IsHaarMeasure := ⟨⟩

/-! ## The weighted product measure is left invariant on `K × B` -/

/-- `δ(a) da`, the weighted Haar measure on `A`. -/
noncomputable def haarAδ : Measure (A n) :=
  (haarA (n := n)).withDensity fun a => (iwasawaDeltaNN a : ℝ≥0∞)

/-- `δ(a) da du` on `A × U`. -/
noncomputable def haarAU : Measure (A n × UU n) := (haarAδ (n := n)).prod haarN

instance instSFinite_haarAδ : SFinite (haarAδ (n := n)) := by
  unfold haarAδ; infer_instance

instance instSFinite_haarAU : SFinite (haarAU (n := n)) := by
  unfold haarAU; infer_instance

/-- Translating the `A` coordinate by `a'` rescales `δ(a) da` by `δ(a')⁻¹`. -/
lemma map_mul_right_haarAδ (a' : A n) :
    Measure.map (· * a') (haarAδ (n := n)) = ((iwasawaDeltaNN a' : ℝ≥0∞))⁻¹ • haarAδ := by
  ext s hs
  have hm : Measurable (· * a' : A n → A n) := measurable_mul_const a'
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul, haarAδ,
    withDensity_apply _ (hm hs), withDensity_apply _ hs]
  have hpt : ∀ x : A n, (iwasawaDeltaNN x : ℝ≥0∞)
      = (iwasawaDeltaNN (x * a') : ℝ≥0∞) * ((iwasawaDeltaNN a' : ℝ≥0∞))⁻¹ := by
    intro x
    rw [iwasawaDeltaNN_mul, ENNReal.coe_mul, mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (iwasawaDeltaNN_ne_zero a'))
        ENNReal.coe_ne_top, mul_one]
  calc ∫⁻ x in (· * a') ⁻¹' s, (iwasawaDeltaNN x : ℝ≥0∞) ∂haarA
      = ∫⁻ x in (· * a') ⁻¹' s,
          (iwasawaDeltaNN (x * a') : ℝ≥0∞) * ((iwasawaDeltaNN a' : ℝ≥0∞))⁻¹ ∂haarA :=
        lintegral_congr fun x => hpt x
    _ = (∫⁻ x in (· * a') ⁻¹' s, (iwasawaDeltaNN (x * a') : ℝ≥0∞) ∂haarA)
          * ((iwasawaDeltaNN a' : ℝ≥0∞))⁻¹ :=
        lintegral_mul_const _ (measurable_iwasawaDeltaENN.comp hm)
    _ = (∫⁻ y in s, (iwasawaDeltaNN y : ℝ≥0∞) ∂haarA) * ((iwasawaDeltaNN a' : ℝ≥0∞))⁻¹ := by
        rw [(measurePreserving_mul_right haarA a').setLIntegral_comp_preimage hs
          measurable_iwasawaDeltaENN]
    _ = ((iwasawaDeltaNN a' : ℝ≥0∞))⁻¹ * ∫⁻ y in s, (iwasawaDeltaNN y : ℝ≥0∞) ∂haarA :=
        mul_comm _ _

lemma measurable_conjAut (a : A n) : Measurable (conjAut a) := (conjAut a).continuous.measurable

/-- Conjugating by `a'` and then translating by `u'` rescales `haarN` by
`δ(a')`. -/
lemma map_conjAut_mul_right_haarN (a' : A n) (u' : UU n) :
    Measure.map (fun u => conjAut a' u * u') (haarN (n := n))
      = (iwasawaDeltaNN a' : ℝ≥0∞) • haarN := by
  have h1 : (fun u => conjAut a' u * u') = (· * u') ∘ (conjAut a') := rfl
  have hδ : (LinearMap.det (adNN a').toLinearMap).toNNReal = iwasawaDeltaNN a' := by
    rw [← iwasawaDelta_eq_det_adNN, ← coe_iwasawaDeltaNN, Real.toNNReal_coe]
  rw [h1, ← Measure.map_map (measurable_mul_const u') (measurable_conjAut a'),
    map_conjAut_haarN, Measure.map_smul, map_mul_right_eq_self, hδ, coe_nnreal_smul]

/-- Right multiplication on `B`, in the coordinates `(a, u)`. -/
noncomputable def rightMulAU (q : A n × UU n) : A n × UU n → A n × UU n :=
  Prod.map (· * q.1) (fun u => conjAut q.1 u * q.2)

lemma measurable_rightMulAU (q : A n × UU n) : Measurable (rightMulAU q) :=
  (measurable_mul_const q.1).prodMap ((measurable_conjAut q.1).mul_const q.2)

/-- **The cancellation.** `δ(a) da du` is invariant under right multiplication
on `B`: the `A` factor loses `δ(a')` and the `U` factor gains it back. -/
lemma map_rightMulAU_haarAU (q : A n × UU n) :
    Measure.map (rightMulAU q) (haarAU (n := n)) = haarAU := by
  have hne : (iwasawaDeltaNN q.1 : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (iwasawaDeltaNN_ne_zero q.1)
  unfold rightMulAU haarAU
  rw [← Measure.map_prod_map _ _ (measurable_mul_const q.1)
      ((measurable_conjAut q.1).mul_const q.2),
    map_mul_right_haarAδ, map_conjAut_mul_right_haarN, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top,
    one_smul]

/-- `(k, (a, u)) ↦ (k, (a u)⁻¹)`, a homeomorphism `K × A × U ≃ₜ K × B`. -/
noncomputable def kauToKB : K n × A n × UU n ≃ₜ K n × BB n :=
  (Homeomorph.refl (K n)).prodCongr (toBBHomeomorph.trans (Homeomorph.inv (BB n)))

lemma kbHomeomorph_kauToKB (x : K n × A n × UU n) :
    kbHomeomorph (kauToKB x) = iwasawaMap x := by
  obtain ⟨k, p⟩ := x
  show iwasawaMap (k, toBBHomeomorph.symm ((toBBHomeomorph p)⁻¹)⁻¹) = iwasawaMap (k, p)
  rw [inv_inv, Homeomorph.symm_apply_apply]

/-- The candidate measure `dk · δ(a) da · du`, carried to `K × B`. -/
noncomputable def candKB : Measure (K n × BB n) :=
  Measure.map kauToKB ((haarK (n := n)).prod haarAU)

instance instIsMulLeftInvariant_candKB : (candKB (n := n)).IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  obtain ⟨k', b'⟩ := h
  set q := toBBHomeomorph.symm (b'⁻¹ : BB n) with hq
  have hbq : toBB q = b'⁻¹ := toBBHomeomorph.apply_symm_apply _
  have hcomm : (fun x => (k', b') * x) ∘ (kauToKB (n := n))
      = kauToKB ∘ Prod.map (k' * ·) (rightMulAU q) := by
    funext x
    obtain ⟨k, p⟩ := x
    show ((k', b') * (k, (toBB p)⁻¹) : K n × BB n) = (k' * k, (toBB (rightMulAU q p))⁻¹)
    rw [Prod.mk_mul_mk]
    congr 1
    show b' * (toBB p)⁻¹ = (toBB (p.1 * q.1, conjAut q.1 p.2 * q.2))⁻¹
    rw [← toBB_mul, hbq, _root_.mul_inv_rev, inv_inv]
  unfold candKB
  rw [Measure.map_map (measurable_const_mul _) kauToKB.measurable, hcomm,
    ← Measure.map_map kauToKB.measurable
      ((measurable_const_mul k').prodMap (measurable_rightMulAU q)),
    ← Measure.map_prod_map _ _ (measurable_const_mul k') (measurable_rightMulAU q),
    map_mul_left_eq_self, map_rightMulAU_haarAU]

instance instIsLocallyFiniteMeasure_haarAδ : IsLocallyFiniteMeasure (haarAδ (n := n)) :=
  IsLocallyFiniteMeasure.withDensity_coe continuous_iwasawaDeltaNN

instance instIsFiniteMeasureOnCompacts_haarAU :
    IsFiniteMeasureOnCompacts (haarAU (n := n)) := by
  unfold haarAU; infer_instance

instance instIsFiniteMeasureOnCompacts_candKB :
    IsFiniteMeasureOnCompacts (candKB (n := n)) :=
  IsFiniteMeasureOnCompacts.map _ kauToKB

/-! ## The integration formula -/

lemma candKB_eq_smul_haarKB :
    candKB (n := n) = haarScalarFactor (candKB (n := n)) haarKB • haarKB :=
  isMulLeftInvariant_eq_smul _ _

lemma haarAδ_univ_ne_zero : (haarAδ (n := n)) Set.univ ≠ 0 := by
  rw [haarAδ, Ne, withDensity_apply_eq_zero' measurable_iwasawaDeltaENN.aemeasurable]
  have hset : {x : A n | (iwasawaDeltaNN x : ℝ≥0∞) ≠ 0} ∩ Set.univ = Set.univ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_univ, and_true, iff_true]
    exact ENNReal.coe_ne_zero.mpr (iwasawaDeltaNN_ne_zero x)
  rw [hset]
  exact IsOpen.measure_ne_zero _ isOpen_univ Set.univ_nonempty

lemma haarScalarFactor_candKB_pos : 0 < haarScalarFactor (candKB (n := n)) haarKB := by
  rw [pos_iff_ne_zero]
  intro h0
  have h := candKB_eq_smul_haarKB (n := n)
  rw [h0, zero_smul] at h
  have huniv : candKB (n := n) Set.univ ≠ 0 := by
    unfold candKB
    rw [Measure.map_apply kauToKB.measurable MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod, haarAU, ← Set.univ_prod_univ,
      Measure.prod_prod]
    exact mul_ne_zero (IsOpen.measure_ne_zero _ isOpen_univ Set.univ_nonempty)
      (mul_ne_zero haarAδ_univ_ne_zero (IsOpen.measure_ne_zero _ isOpen_univ Set.univ_nonempty))
  exact huniv (by simp [h])

/-- **The Iwasawa integration formula** (Lang's ordering `g = k · a · u`).
Pushing `dk · δ(a) da · du` forward along `(k, a, u) ↦ k a u` gives Haar measure
on `GL_n(ℝ)`, up to a positive constant. Here `δ(a) = ∏_{i<j} aᵢ / aⱼ`
(`iwasawaDelta`). -/
theorem map_iwasawaMap_haar :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (iwasawaMap (n := n))
          ((haarK (n := n)).prod
            (((haarA (n := n)).withDensity fun a => (iwasawaDeltaNN a : ℝ≥0∞)).prod haarN))
        = c • haarG := by
  refine ⟨haarScalarFactor (candKB (n := n)) haarKB, haarScalarFactor_candKB_pos, ?_⟩
  set c := haarScalarFactor (candKB (n := n)) haarKB
  have h1 : Measure.map kbHomeomorph (candKB (n := n))
      = Measure.map iwasawaMap ((haarK (n := n)).prod haarAU) := by
    unfold candKB
    rw [Measure.map_map kbHomeomorph.measurable kauToKB.measurable]
    congr 1
    funext x
    exact kbHomeomorph_kauToKB x
  have h2 : Measure.map kbHomeomorph (haarKB (n := n)) = haarG := by
    unfold haarKB
    rw [Measure.map_map kbHomeomorph.measurable kbHomeomorph.symm.measurable,
      kbHomeomorph.self_comp_symm, Measure.map_id]
  have h3 : candKB (n := n) = c • haarKB := candKB_eq_smul_haarKB
  show Measure.map iwasawaMap ((haarK (n := n)).prod haarAU) = c • haarG
  rw [← h1, h3, Measure.map_smul, h2]

/-- **The Iwasawa integration formula, integral form.** For every measurable
`f : GL_n(ℝ) → [0, ∞]`,
`c · ∫ f dg = ∫_K ∫_A δ(a) ∫_U f(k a u) du da dk`. -/
theorem lintegral_iwasawa :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : G n → ℝ≥0∞, Measurable f →
      (c : ℝ≥0∞) * ∫⁻ g, f g ∂haarG
        = ∫⁻ k, ∫⁻ a, (iwasawaDeltaNN a : ℝ≥0∞) *
            ∫⁻ u, f (iwasawaMap (k, a, u)) ∂haarN ∂haarA ∂haarK := by
  obtain ⟨c, hc, h⟩ := map_iwasawaMap_haar (n := n)
  refine ⟨c, hc, fun f hf => ?_⟩
  have hΦ : Measurable (iwasawaMap (n := n)) := continuous_iwasawaMap.measurable
  have hF : Measurable fun x : K n × A n × UU n => f (iwasawaMap x) := hf.comp hΦ
  have hL : (c : ℝ≥0∞) * ∫⁻ g, f g ∂haarG = ∫⁻ g, f g ∂(c • haarG) := by
    rw [lintegral_smul_measure]; rfl
  rw [hL, ← h, lintegral_map hf hΦ, lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun k => ?_
  have hFk : Measurable fun p : A n × UU n => f (iwasawaMap (k, p)) :=
    hF.comp measurable_prodMk_left
  rw [lintegral_prod _ hFk.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_iwasawaDeltaENN
      hFk.lintegral_prod_right']
  rfl

/-! ## The Jorgenson-Lang ordering `g = u · a · k` -/

/-- The Jorgenson-Lang product map `(u, a, k) ↦ u · a · k`. -/
noncomputable def iwasawaMapJL (p : UU n × A n × K n) : G n :=
  UU.toG p.1 * A.toG p.2.1 * K.toG p.2.2

lemma iwasawaMapJL_eq (p : UU n × A n × K n) :
    iwasawaMapJL p = (iwasawaMap (p.2.2⁻¹, p.2.1⁻¹, p.1⁻¹))⁻¹ := by
  apply Subtype.ext
  show p.1.1 * p.2.1.1 * p.2.2.1 = (p.2.2.1.transpose * p.2.1.1⁻¹ * p.1.1⁻¹)⁻¹
  have hk : p.2.2.1.transpose = p.2.2.1⁻¹ :=
    (Iwasawa.IsOrthogonal.matInv_eq_transpose p.2.2.2).symm
  have hu : IsUnit p.1.1.det := Ne.isUnit p.1.2.det_ne_zero
  have ha : IsUnit p.2.1.1.det := isUnit_iff_ne_zero.mpr p.2.1.2.det_pos.ne'
  have hk' : IsUnit p.2.2.1.det := isUnit_iff_ne_zero.mpr p.2.2.2.det_ne_zero
  rw [hk, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu,
    Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.nonsing_inv_nonsing_inv _ hk',
    Matrix.mul_assoc]

/-- Inverting `δ(a)⁻¹ da` gives `δ(a) da`. -/
lemma map_inv_haarA_withDensity_inv :
    Measure.map Inv.inv
        ((haarA (n := n)).withDensity fun a => ((iwasawaDeltaNN a)⁻¹ : ℝ≥0) )
      = haarAδ := by
  ext s hs
  rw [Measure.map_apply measurable_inv hs, withDensity_apply _ (measurable_inv hs), haarAδ,
    withDensity_apply _ hs]
  have hpt : ∀ x : A n, (((iwasawaDeltaNN x)⁻¹ : ℝ≥0) : ℝ≥0∞)
      = (iwasawaDeltaNN x⁻¹ : ℝ≥0∞) := fun x => by rw [iwasawaDeltaNN_inv]
  rw [lintegral_congr fun x => hpt x]
  exact (measurePreserving_inv haarA).setLIntegral_comp_preimage hs measurable_iwasawaDeltaENN

/-- Reordering a triple product: `(x, (y, z)) ↦ (z, (y, x))`. -/
lemma map_reorder_prod {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa]
    [SFinite μb] [SFinite μc] :
    Measure.map (fun p : α × β × γ => (p.2.2, p.2.1, p.1)) (μa.prod (μb.prod μc))
      = μc.prod (μb.prod μa) := by
  have e1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb μc)
  have e2 := (Measure.measurePreserving_swap (μ := μa.prod μb) (ν := μc))
  have e3 := (MeasurePreserving.id μc).prod (Measure.measurePreserving_swap (μ := μa) (ν := μb))
  have e := e3.comp (e2.comp e1)
  rw [← e.map_eq]
  rfl

/-- **The Iwasawa integration formula, Jorgenson-Lang ordering.** Pushing
`du · δ(a)⁻¹ da · dk` forward along `(u, a, k) ↦ u a k` gives Haar measure on
`GL_n(ℝ)`, up to a positive constant. -/
theorem map_iwasawaMapJL_haar :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (iwasawaMapJL (n := n))
          ((haarN (n := n)).prod
            (((haarA (n := n)).withDensity fun a => ((iwasawaDeltaNN a)⁻¹ : ℝ≥0)).prod
              haarK))
        = c • haarG := by
  obtain ⟨c, hc, h⟩ := map_iwasawaMap_haar (n := n)
  refine ⟨c, hc, ?_⟩
  have hR : Measure.map (fun p : UU n × A n × K n => (p.2.2⁻¹, p.2.1⁻¹, p.1⁻¹))
      ((haarN (n := n)).prod
        (((haarA (n := n)).withDensity fun a => ((iwasawaDeltaNN a)⁻¹ : ℝ≥0)).prod haarK))
      = (haarK (n := n)).prod (haarAδ.prod haarN) := by
    have hsplit : (fun p : UU n × A n × K n => (p.2.2⁻¹, p.2.1⁻¹, p.1⁻¹))
        = (fun p : UU n × A n × K n => (p.2.2, p.2.1, p.1))
          ∘ Prod.map Inv.inv (Prod.map Inv.inv Inv.inv) := rfl
    rw [hsplit, ← Measure.map_map (by fun_prop)
        (measurable_inv.prodMap (measurable_inv.prodMap measurable_inv)),
      ← Measure.map_prod_map _ _ measurable_inv (measurable_inv.prodMap measurable_inv),
      ← Measure.map_prod_map _ _ measurable_inv measurable_inv,
      map_inv_eq_self (haarN (n := n)), map_inv_eq_self (haarK (n := n)),
      map_inv_haarA_withDensity_inv, map_reorder_prod]
  have hJL : (iwasawaMapJL (n := n))
      = Inv.inv ∘ iwasawaMap ∘ (fun p : UU n × A n × K n => (p.2.2⁻¹, p.2.1⁻¹, p.1⁻¹)) := by
    funext p; exact iwasawaMapJL_eq p
  rw [hJL, ← Measure.map_map measurable_inv (continuous_iwasawaMap.measurable.comp (by fun_prop)),
    ← Measure.map_map continuous_iwasawaMap.measurable (by fun_prop), hR]
  show Measure.map Inv.inv (Measure.map iwasawaMap ((haarK (n := n)).prod haarAU)) = c • haarG
  rw [show Measure.map iwasawaMap ((haarK (n := n)).prod haarAU) = c • haarG from h,
    Measure.map_smul, map_inv_eq_self]

/-! ## The modular character of `B = A · U`

`δ` is the modular character of `B` on `A`, in Mathlib's convention
`map (· * g) μ = modularCharacterFun g • μ`. -/

instance instIsOpenPosMeasure_haarAδ : (haarAδ (n := n)).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [haarAδ, Ne, withDensity_apply_eq_zero' measurable_iwasawaDeltaENN.aemeasurable]
  have hset : {x : A n | (iwasawaDeltaNN x : ℝ≥0∞) ≠ 0} ∩ U = U := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_right_iff_imp]
    exact fun _ => ENNReal.coe_ne_zero.mpr (iwasawaDeltaNN_ne_zero x)
  rw [hset]
  exact hU.measure_ne_zero haarA hne

instance instIsOpenPosMeasure_haarAU : (haarAU (n := n)).IsOpenPosMeasure := by
  unfold haarAU; infer_instance

/-- `(a, u) ↦ (a u)⁻¹`, a homeomorphism `A × U ≃ₜ B`. -/
noncomputable def invToBB : A n × UU n ≃ₜ BB n :=
  toBBHomeomorph.trans (Homeomorph.inv (BB n))

/-- A left Haar measure on `B`: `δ(a) da du` carried over by `(a, u) ↦ (a u)⁻¹`. -/
noncomputable def haarBB : Measure (BB n) := Measure.map invToBB haarAU

instance instIsMulLeftInvariant_haarBB : (haarBB (n := n)).IsMulLeftInvariant := by
  refine ⟨fun b' => ?_⟩
  set q := toBBHomeomorph.symm (b'⁻¹ : BB n) with hq
  have hbq : toBB q = b'⁻¹ := toBBHomeomorph.apply_symm_apply _
  have hcomm : (fun x => b' * x) ∘ (invToBB (n := n)) = invToBB ∘ rightMulAU q := by
    funext p
    show b' * (toBB p)⁻¹ = (toBB (p.1 * q.1, conjAut q.1 p.2 * q.2))⁻¹
    rw [← toBB_mul, hbq, _root_.mul_inv_rev, inv_inv]
  unfold haarBB
  rw [Measure.map_map (measurable_const_mul _) invToBB.measurable, hcomm,
    ← Measure.map_map invToBB.measurable (measurable_rightMulAU q), map_rightMulAU_haarAU]

instance instIsFiniteMeasureOnCompacts_haarBB : IsFiniteMeasureOnCompacts (haarBB (n := n)) :=
  IsFiniteMeasureOnCompacts.map _ invToBB

instance instIsOpenPosMeasure_haarBB : (haarBB (n := n)).IsOpenPosMeasure :=
  invToBB.continuous.isOpenPosMeasure_map invToBB.surjective

instance instIsHaarMeasure_haarBB : (haarBB (n := n)).IsHaarMeasure := ⟨⟩

lemma toBB_inv_one (a : A n) : (toBB (a, 1))⁻¹ = toBB (a⁻¹, 1) := by
  apply Subtype.ext; apply Subtype.ext
  show (((toBB (a, 1) : BB n) : G n) : Matrix (Fin n) (Fin n) ℝ)⁻¹
    = (((toBB (a⁻¹, 1) : BB n) : G n) : Matrix (Fin n) (Fin n) ℝ)
  rw [toBB_val, toBB_val]
  show (a.1 * 1)⁻¹ = a.1⁻¹ * 1
  rw [Matrix.mul_one, Matrix.mul_one]

/-- Right multiplication by `a ∈ A ⊆ B` multiplies `haarBB` by `δ(a)`. -/
lemma map_mul_right_toBB_haarBB (a : A n) :
    Measure.map (· * toBB (a, 1)) (haarBB (n := n)) = (iwasawaDeltaNN a : ℝ≥0∞) • haarBB := by
  have hcomm : (· * toBB (a, 1)) ∘ (invToBB (n := n)) = invToBB ∘ Prod.map (· * a⁻¹) id := by
    funext p
    show (toBB p)⁻¹ * toBB (a, 1) = (toBB (p.1 * a⁻¹, p.2))⁻¹
    rw [← inv_inv (toBB (a, 1)), ← _root_.mul_inv_rev, toBB_inv_one, toBB_mul]
    congr 2
    ext1
    · exact mul_comm _ _
    · show conjAut p.1 1 * p.2 = p.2
      rw [map_one, one_mul]
  have hδinv : ((iwasawaDeltaNN a⁻¹ : ℝ≥0∞))⁻¹ = (iwasawaDeltaNN a : ℝ≥0∞) := by
    rw [iwasawaDeltaNN_inv, ENNReal.coe_inv (iwasawaDeltaNN_ne_zero a), inv_inv]
  unfold haarBB haarAU
  rw [Measure.map_map (measurable_mul_const _) invToBB.measurable, hcomm,
    ← Measure.map_map invToBB.measurable ((measurable_mul_const _).prodMap measurable_id),
    ← Measure.map_prod_map _ _ (measurable_mul_const _) measurable_id, Measure.map_id,
    map_mul_right_haarAδ, hδinv, Measure.prod_smul_left, Measure.map_smul]

/-- **The modular character of `B = A · U` on `A` is `δ`.** Mathlib's
`Measure.modularCharacterFun`, computed on `B`, is the positive root product
`δ(a) = ∏_{i<j} aᵢ / aⱼ`. -/
theorem modularCharacterFun_toBB (a : A n) :
    Measure.modularCharacterFun (toBB (a, 1)) = iwasawaDeltaNN a := by
  have h : Measure.map (· * toBB (a, 1)) (haarBB (n := n)) = iwasawaDeltaNN a • haarBB := by
    rw [map_mul_right_toBB_haarBB, coe_nnreal_smul]
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (haarBB (n := n))]
  simp only [h]
  rw [haarScalarFactor_smul, haarScalarFactor_self, smul_eq_mul, mul_one]

/-! ## Axiom check

Each `#print axioms` below is wrapped in `#guard_msgs`, so `lake build` fails if one of
these results ever depends on `sorryAx` or on an axiom beyond the standard three. -/

/-- info: 'IwasawaCoC.Complete.modularCharacterFun_UU_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modularCharacterFun_UU_eq_one

/-- info: 'IwasawaCoC.Complete.modularCharacterFun_K_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modularCharacterFun_K_eq_one

/-- info: 'IwasawaCoC.Complete.isInvInvariant_of_isMulRightInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isInvInvariant_of_isMulRightInvariant

/-- info: 'IwasawaCoC.Complete.toBBHomeomorph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toBBHomeomorph

/-- info: 'IwasawaCoC.Complete.kbHomeomorph_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kbHomeomorph_mul

/-- info: 'IwasawaCoC.Complete.map_rightMulAU_haarAU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_rightMulAU_haarAU

/-- info: 'IwasawaCoC.Complete.map_iwasawaMap_haar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_iwasawaMap_haar

/-- info: 'IwasawaCoC.Complete.lintegral_iwasawa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lintegral_iwasawa

/-- info: 'IwasawaCoC.Complete.map_iwasawaMapJL_haar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_iwasawaMapJL_haar

/-- info: 'IwasawaCoC.Complete.modularCharacterFun_toBB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modularCharacterFun_toBB

end Complete
end IwasawaCoC

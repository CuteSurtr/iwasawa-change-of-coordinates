/-
T1-6: explicit product formula for `LinearMap.det (adNN a)`.

Target:

  theorem ad_on_n_det_eq_pair_product (a : A n) :
    LinearMap.det (adNN a).toLinearMap =
      ∏ ij ∈ Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2),
        (a.1 ij.1 ij.1) / (a.1 ij.2 ij.2)

Per MathlibInfrastructureMap.md §1c "Distribution Haar character":
`distribHaarChar N (a) = |det Ad(a)|_𝔫|`. This file computes the
RHS explicitly. In the current project structure this is the
positive-root product needed by the future Jacobian/Haar layer; it is
not yet the determinant theorem for the full derivative
`iwasawaMatrixLeibnizCLM k a u`.

Strategy: build a `Basis (nnIndex n) ℝ (NN n)` indexed by ordered pairs
`{(i, j) | i < j}` with basis vector `⟨Matrix.single i j 1, _⟩`; then
`adNN a` acts diagonally on this basis with eigenvalue
`(a.1 i i / a.1 j j)` (from `adNN_entry` in T1-4 L2). Then
`LinearMap.det_toMatrix` + `Matrix.det_diagonal` close the formula.

Critical typeclass note: use `linfty op` matrix norms upfront (per
session post-mortem on previous-session typeclass conflict). All
Matrix.NormedRing-dependent lemmas need this.

Per user-specified routing options:
(a) `Module.Free` for `NN n` — confirmed available via `inferInstance`.
(b) `Matrix.stdBasis` exists for full matrices; need restriction.
(c) Manual basis via `Basis.mk` + `LinearIndependent` + spanning.

We use (c) directly with care, building on the previous session's
attempt but with cleaner tactics (avoiding `mem_span_range_iff_exists_fun`
which is not the canonical Mathlib name).
-/

import iwasawa_change_of_coords.IwasawaMFDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Matrix.Basis

namespace IwasawaCoC

open Matrix Iwasawa Set Function Finset Module
open scoped Manifold ContDiff RightActions Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

section JacobianExplicit

-- Local matrix norm: linfty op (per session post-mortem).
attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- Index type for the basis of strictly upper triangular matrices:
ordered pairs `(i, j)` with `i < j`. -/
def nnIndex (n : ℕ) : Type := { ij : Fin n × Fin n // ij.1 < ij.2 }

instance : Fintype (nnIndex n) :=
  inferInstanceAs (Fintype {ij : Fin n × Fin n // ij.1 < ij.2})

instance : DecidableEq (nnIndex n) :=
  inferInstanceAs (DecidableEq {ij : Fin n × Fin n // ij.1 < ij.2})

/-- Lexicographic order on strict upper index pairs.  This is used only
to apply triangular determinant lemmas to `NN` transport matrices. -/
@[reducible] noncomputable def nnIndexLexLinearOrder (n : ℕ) : LinearOrder (nnIndex n) :=
  LinearOrder.lift' (fun ij : nnIndex n => (toLex (ij.1.1, ij.1.2) : Lex (Fin n × Fin n)))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg ofLex h)

/-- The basis vector indexed by `⟨(i, j), hij⟩` is `Matrix.single i j 1`,
viewed as an element of `NN n` (using `hij : i < j` to verify
strict-upper-triangularity). -/
def nnBasisVec (ij : nnIndex n) : NN n :=
  ⟨Matrix.single ij.1.1 ij.1.2 (1 : ℝ), by
    intro i' j' hji'
    show Matrix.single ij.1.1 ij.1.2 (1 : ℝ) i' j' = 0
    -- For j' ≤ i', this entry is zero unless (ij.1.1, ij.1.2) = (i', j').
    -- But then j' = ij.1.2 > ij.1.1 = i', contradicting j' ≤ i'.
    rw [Matrix.single_apply]
    split_ifs with h
    · exfalso
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact absurd hji' (not_le.mpr ij.2)
    · rfl⟩

@[simp] lemma nnBasisVec_val (ij : nnIndex n) :
    (nnBasisVec ij : Matrix (Fin n) (Fin n) ℝ) = Matrix.single ij.1.1 ij.1.2 1 := rfl

/-! ## Linear independence of nnBasisVec

Reduce to linear independence of the underlying `Matrix.single` family
via `LinearIndependent.of_comp` with `(NN n).subtype` (the inclusion
into `Matrix _ _ ℝ`). The matrix-level family `(i, j) ↦ single i j 1`
restricted to `{i < j}` is linearly independent because it is a
subfamily of the standard basis `Matrix.stdBasis`. -/

private lemma nnBasisVec_linearIndependent :
    LinearIndependent ℝ (nnBasisVec : nnIndex n → NN n) := by
  -- The composition `(NN n).subtype ∘ nnBasisVec` is `fun ij ↦ single ij.1.1 ij.1.2 1`.
  -- We use `LinearIndependent.of_comp` to reduce.
  apply LinearIndependent.of_comp (NN n).subtype
  -- Goal: LinearIndependent ℝ ((↑) ∘ nnBasisVec : nnIndex n → Matrix _ _ ℝ).
  -- The function is `fun ij => single ij.1.1 ij.1.2 1`.
  -- This factors as `Matrix.stdBasis ℝ (Fin n) (Fin n)` composed with the
  -- injection `nnIndex n → Fin n × Fin n` (the underlying pair).
  have h_eq : ((NN n).subtype ∘ (nnBasisVec : nnIndex n → NN n)) =
      (Matrix.stdBasis ℝ (Fin n) (Fin n)) ∘ (fun ij : nnIndex n => ij.1) := by
    funext ij
    show ((nnBasisVec ij : NN n) : Matrix (Fin n) (Fin n) ℝ) =
         Matrix.stdBasis ℝ (Fin n) (Fin n) ij.1
    rw [nnBasisVec_val, Matrix.stdBasis_eq_single]
  rw [h_eq]
  -- Composition of linearly-independent (`stdBasis.linearIndependent`)
  -- with an injection is linearly independent.
  exact (Matrix.stdBasis ℝ (Fin n) (Fin n)).linearIndependent.comp _
    (fun a b hab => Subtype.ext hab)

/-! ## Spanning by nnBasisVec

Every `X ∈ NN n` is a finite linear combination of the basis vectors,
with coefficients `X.1 i j` for `(i, j) ∈ nnIndex n`. -/

private lemma nnBasisVec_span_top :
    ⊤ ≤ Submodule.span ℝ (Set.range (nnBasisVec : nnIndex n → NN n)) := by
  -- Use `Submodule.top_le_span_range_iff_forall_exists_fun`: reduces to
  -- showing every X has an explicit linear combination representation:
  -- `X = ∑_{ij : i < j} X.1 ij.1 ij.2 • nnBasisVec ij`.
  rw [Submodule.top_le_span_range_iff_forall_exists_fun]
  intro X
  refine ⟨fun ij : nnIndex n => X.1 ij.1.1 ij.1.2, ?_⟩
  -- Goal: ∑ ij, X.1 ij.1.1 ij.1.2 • nnBasisVec ij = X (in NN n).
  -- Use Subtype.ext to reduce to matrix equality, then entrywise.
  apply Subtype.ext
  -- Goal: (∑ ij, X.1 ij.1.1 ij.1.2 • nnBasisVec ij).val = X.val
  rw [AddSubmonoid.coe_finset_sum]
  ext i j
  -- Goal: (∑ ij, (X.1 ij.1.1 ij.1.2 • nnBasisVec ij).val) i j = X.val i j
  -- After Matrix.ext, the i j is auto-distributed into the sum.
  -- Each summand: scalar * single ij.1.1 ij.1.2 1 i j.
  simp only [Matrix.sum_apply, SetLike.val_smul, nnBasisVec_val,
             Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  -- Goal: ∑ ij, X.1 ij.1.1 ij.1.2 * (if ij.1.1 = i ∧ ij.1.2 = j then 1 else 0) = X.1 i j
  by_cases hij : i < j
  · -- i < j: unique nnIndex element is ⟨(i, j), hij⟩, contributing X.1 i j.
    -- Use `convert Finset.sum_eq_single_of_mem` (lenient unification).
    convert Finset.sum_eq_single_of_mem
      (a := (⟨(i, j), hij⟩ : nnIndex n))
      (s := (Finset.univ : Finset (nnIndex n)))
      (f := fun b : nnIndex n => X.1 b.1.1 b.1.2 *
        (if b.1.1 = i ∧ b.1.2 = j then (1 : ℝ) else 0))
      (Finset.mem_univ _) ?_ using 1
    · -- f ⟨(i, j), hij⟩ = X.1 i j (the selected term).
      simp
    · -- Others-vanish hypothesis.
      intro b _ hb
      show X.1 b.1.1 b.1.2 * (if b.1.1 = i ∧ b.1.2 = j then (1 : ℝ) else 0) = 0
      have hne : ¬ (b.1.1 = i ∧ b.1.2 = j) := by
        rintro ⟨h1, h2⟩
        exact hb (Subtype.ext (Prod.ext h1 h2))
      rw [if_neg hne, mul_zero]
  · -- j ≤ i: X.1 i j = 0 and each summand is 0.
    push Not at hij
    rw [X.2 i j hij]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h : b.1.1 = i ∧ b.1.2 = j
    · -- b.1 = (i, j) means i < j (from b's index property), contradicting hij.
      exfalso
      obtain ⟨h1, h2⟩ := h
      have hbij : b.1.1 < b.1.2 := b.2
      rw [h1, h2] at hbij
      exact absurd hbij (not_lt.mpr hij)
    · rw [if_neg h, mul_zero]

/-- The basis of `NN n` indexed by `nnIndex n`. -/
noncomputable def nnBasis : Basis (nnIndex n) ℝ (NN n) :=
  Basis.mk nnBasisVec_linearIndependent nnBasisVec_span_top

@[simp] lemma nnBasis_apply (ij : nnIndex n) :
    nnBasis ij = nnBasisVec ij := by
  show Basis.mk nnBasisVec_linearIndependent nnBasisVec_span_top ij = nnBasisVec ij
  simp [Module.Basis.coe_mk]

lemma nnBasisVec_apply_upper_index (row col : nnIndex n) :
    (nnBasisVec col : Matrix (Fin n) (Fin n) ℝ) row.1.1 row.1.2 =
      if row = col then 1 else 0 := by
  rw [nnBasisVec_val, Matrix.single_apply]
  by_cases h : row = col
  · subst h
    simp
  · have hpairs : ¬ (col.1.1 = row.1.1 ∧ col.1.2 = row.1.2) := by
      rintro ⟨h1, h2⟩
      exact h (Subtype.ext (Prod.ext h1.symm h2.symm))
    simp [hpairs, h]

lemma nnBasis_repr_apply (X : NN n) (ij : nnIndex n) :
    nnBasis.repr X ij = X.1 ij.1.1 ij.1.2 := by
  have h := congrArg
    (fun Y : NN n => (Y : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
    (Module.Basis.sum_repr nnBasis X)
  change ((↑(∑ i, (nnBasis.repr X) i • nnBasis i : NN n) :
      Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) =
      X.1 ij.1.1 ij.1.2 at h
  rw [AddSubmonoid.coe_finset_sum] at h
  simp only [SetLike.val_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    nnBasis_apply, nnBasisVec_val, Matrix.single_apply] at h
  rw [Finset.sum_eq_single ij] at h
  · simpa using h
  · intro b _ hb
    have hne : ¬ (b.1.1 = ij.1.1 ∧ b.1.2 = ij.1.2) := by
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    rw [if_neg hne, mul_zero]
  · intro hij
    simp at hij

/-! ## Basis of `Sk n`

We coordinatize skew-symmetric matrices by their strict upper entries.
The inverse reconstruction sends upper entries to `Eᵢⱼ - Eⱼᵢ`. -/

private def skOfUpperMatrix (c : nnIndex n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if hij : i < j then c ⟨(i, j), hij⟩
    else if hji : j < i then -c ⟨(j, i), hji⟩
    else 0

private lemma skOfUpperMatrix_skew (c : nnIndex n → ℝ) :
    (skOfUpperMatrix c).transpose = -(skOfUpperMatrix c) := by
  ext i j
  unfold skOfUpperMatrix
  rcases lt_trichotomy i j with hij | hEq | hji
  · simp [hij, not_lt_of_gt hij]
  · subst hEq
    simp
  · simp [hji, not_lt_of_gt hji]

noncomputable def skOfUpper (c : nnIndex n → ℝ) : Sk n :=
  ⟨skOfUpperMatrix c, skOfUpperMatrix_skew c⟩

@[simp] lemma skOfUpper_val (c : nnIndex n → ℝ) :
    (skOfUpper c : Matrix (Fin n) (Fin n) ℝ) = skOfUpperMatrix c := rfl

lemma skOfUpper_apply_upper (c : nnIndex n → ℝ) {i j : Fin n} (hij : i < j) :
    (skOfUpper c : Matrix (Fin n) (Fin n) ℝ) i j = c ⟨(i, j), hij⟩ := by
  simp [skOfUpper, skOfUpperMatrix, hij]

lemma skOfUpper_apply_lower (c : nnIndex n → ℝ) {i j : Fin n} (hji : j < i) :
    (skOfUpper c : Matrix (Fin n) (Fin n) ℝ) i j = -c ⟨(j, i), hji⟩ := by
  simp [skOfUpper, skOfUpperMatrix, hji, not_lt_of_gt hji]

@[simp] lemma skOfUpper_apply_diag (c : nnIndex n → ℝ) (i : Fin n) :
    (skOfUpper c : Matrix (Fin n) (Fin n) ℝ) i i = 0 := by
  simp [skOfUpper, skOfUpperMatrix]

lemma sk_mem_apply_swap (X : Sk n) (i j : Fin n) :
    X.1 j i = -X.1 i j := by
  simpa [Matrix.transpose_apply] using congrArg (fun M => M i j) X.2

@[simp] lemma sk_mem_apply_diag (X : Sk n) (i : Fin n) :
    X.1 i i = 0 := by
  have h := sk_mem_apply_swap X i i
  linarith

/-- Skew-symmetric matrices are linearly equivalent to their strict upper entries. -/
noncomputable def skCoordLinearEquiv : Sk n ≃ₗ[ℝ] (nnIndex n → ℝ) where
  toFun := fun X ij => X.1 ij.1.1 ij.1.2
  invFun := skOfUpper
  left_inv := by
    intro X
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | hEq | hji
    · simp [skOfUpper_apply_upper _ hij]
    · subst hEq
      simp
    · rw [skOfUpper_apply_lower _ hji]
      have hswap := sk_mem_apply_swap X j i
      linarith
  right_inv := by
    intro c
    funext ij
    exact skOfUpper_apply_upper c ij.2
  map_add' := by
    intro X Y
    rfl
  map_smul' := by
    intro c X
    rfl

@[simp] lemma skCoordLinearEquiv_apply (X : Sk n) (ij : nnIndex n) :
    skCoordLinearEquiv X ij = X.1 ij.1.1 ij.1.2 := rfl

@[simp] lemma skCoordLinearEquiv_symm_apply_upper
    (c : nnIndex n → ℝ) {i j : Fin n} (hij : i < j) :
    ((skCoordLinearEquiv (n := n)).symm c : Matrix (Fin n) (Fin n) ℝ) i j =
      c ⟨(i, j), hij⟩ :=
  skOfUpper_apply_upper c hij

@[simp] lemma skCoordLinearEquiv_symm_apply_lower
    (c : nnIndex n → ℝ) {i j : Fin n} (hji : j < i) :
    ((skCoordLinearEquiv (n := n)).symm c : Matrix (Fin n) (Fin n) ℝ) i j =
      -c ⟨(j, i), hji⟩ :=
  skOfUpper_apply_lower c hji

@[simp] lemma skCoordLinearEquiv_symm_apply_diag
    (c : nnIndex n → ℝ) (i : Fin n) :
    ((skCoordLinearEquiv (n := n)).symm c : Matrix (Fin n) (Fin n) ℝ) i i = 0 :=
  skOfUpper_apply_diag c i

/-- The standard basis of `Sk n`, indexed by strict upper pairs. -/
noncomputable def skBasis : Basis (nnIndex n) ℝ (Sk n) :=
  (Pi.basisFun ℝ (nnIndex n)).map (skCoordLinearEquiv (n := n)).symm

@[simp] lemma skBasis_apply (ij : nnIndex n) :
    skBasis ij = (skCoordLinearEquiv (n := n)).symm (Pi.single ij (1 : ℝ)) := by
  rw [skBasis, Module.Basis.map_apply, Pi.basisFun_apply]

lemma skBasis_repr_apply (X : Sk n) (ij : nnIndex n) :
    (skBasis (n := n)).repr X ij = X.1 ij.1.1 ij.1.2 := by
  rw [← Module.Basis.equivFun_apply]
  simp [skBasis, skCoordLinearEquiv_apply]

lemma skBasis_apply_upper (ij : nnIndex n) :
    (skBasis ij : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2 = 1 := by
  rw [skBasis_apply]
  rw [skCoordLinearEquiv_symm_apply_upper _ ij.2]
  have hidx : (⟨(ij.1.1, ij.1.2), ij.2⟩ : nnIndex n) = ij := Subtype.ext rfl
  rw [hidx, Pi.single_eq_same]

lemma skBasis_apply_lower (ij : nnIndex n) :
    (skBasis ij : Matrix (Fin n) (Fin n) ℝ) ij.1.2 ij.1.1 = -1 := by
  rw [skBasis_apply]
  rw [skCoordLinearEquiv_symm_apply_lower _ ij.2]
  have hidx : (⟨(ij.1.1, ij.1.2), ij.2⟩ : nnIndex n) = ij := Subtype.ext rfl
  rw [hidx, Pi.single_eq_same]

@[simp] lemma skBasis_apply_diag (ij : nnIndex n) (i : Fin n) :
    (skBasis ij : Matrix (Fin n) (Fin n) ℝ) i i = 0 := by
  rw [skBasis_apply]
  simp

lemma skBasis_apply_upper_index (row col : nnIndex n) :
    (skBasis col : Matrix (Fin n) (Fin n) ℝ) row.1.1 row.1.2 =
      if row = col then 1 else 0 := by
  rw [skBasis_apply]
  rw [skCoordLinearEquiv_symm_apply_upper _ row.2]
  have hrow : (⟨(row.1.1, row.1.2), row.2⟩ : nnIndex n) = row := Subtype.ext rfl
  rw [hrow]
  by_cases h : row = col
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    simp [h]

lemma skBasis_apply_lower_index (row col : nnIndex n) :
    (skBasis col : Matrix (Fin n) (Fin n) ℝ) row.1.2 row.1.1 =
      if row = col then -1 else 0 := by
  rw [skBasis_apply]
  rw [skCoordLinearEquiv_symm_apply_lower _ row.2]
  have hrow : (⟨(row.1.1, row.1.2), row.2⟩ : nnIndex n) = row := Subtype.ext rfl
  rw [hrow]
  by_cases h : row = col
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    simp [h]

/-! ## Source basis for the Iwasawa derivative

The source of `iwasawaMatrixLeibnizCLM` is indexed by matrix positions:
lower entries use `Sk`, diagonal entries use `Fin n → ℝ`, and upper
entries use `NN`. -/

noncomputable def iwasawaSourceBasisProd :
    Basis ((nnIndex n) ⊕ ((Fin n) ⊕ (nnIndex n))) ℝ
      ((Sk n) × ((Fin n → ℝ) × (NN n))) :=
  skBasis.prod ((Pi.basisFun ℝ (Fin n)).prod nnBasis)

/-- Reindex the product source basis by matrix positions. -/
def iwasawaSourceIndexEquiv :
    ((nnIndex n) ⊕ ((Fin n) ⊕ (nnIndex n))) ≃ (Fin n × Fin n) where
  toFun
    | Sum.inl ij => (ij.1.2, ij.1.1)
    | Sum.inr (Sum.inl i) => (i, i)
    | Sum.inr (Sum.inr ij) => (ij.1.1, ij.1.2)
  invFun := fun p =>
    if hp : p.1 < p.2 then
      Sum.inr (Sum.inr ⟨p, hp⟩)
    else if hp' : p.2 < p.1 then
      Sum.inl ⟨(p.2, p.1), hp'⟩
    else
      Sum.inr (Sum.inl p.1)
  left_inv := by
    intro s
    rcases s with ij | (i | ij)
    · simp [not_lt_of_gt ij.2, ij.2]
    · simp
    · simp [ij.2]
  right_inv := by
    intro p
    rcases p with ⟨i, j⟩
    rcases lt_trichotomy i j with hp | hp | hp
    · simp [hp]
    · subst hp
      simp
    · simp [not_lt_of_gt hp, hp]

noncomputable def iwasawaSourceBasis :
    Basis (Fin n × Fin n) ℝ ((Sk n) × ((Fin n → ℝ) × (NN n))) :=
  iwasawaSourceBasisProd.reindex (iwasawaSourceIndexEquiv (n := n))

lemma iwasawaSourceIndexEquiv_symm_lower {i j : Fin n} (hji : j < i) :
    (iwasawaSourceIndexEquiv (n := n)).symm (i, j) =
      Sum.inl (⟨(j, i), hji⟩ : nnIndex n) := by
  unfold iwasawaSourceIndexEquiv
  change (if hij : i < j then
      Sum.inr (Sum.inr (⟨(i, j), hij⟩ : nnIndex n))
    else if hji' : j < i then
      Sum.inl (⟨(j, i), hji'⟩ : nnIndex n)
    else
      Sum.inr (Sum.inl i)) =
      Sum.inl (⟨(j, i), hji⟩ : nnIndex n)
  rw [dif_neg (not_lt_of_gt hji), dif_pos hji]

lemma iwasawaSourceIndexEquiv_symm_diag (i : Fin n) :
    (iwasawaSourceIndexEquiv (n := n)).symm (i, i) =
      Sum.inr (Sum.inl i) := by
  simp [iwasawaSourceIndexEquiv]

lemma iwasawaSourceIndexEquiv_symm_upper {i j : Fin n} (hij : i < j) :
    (iwasawaSourceIndexEquiv (n := n)).symm (i, j) =
      Sum.inr (Sum.inr (⟨(i, j), hij⟩ : nnIndex n)) := by
  unfold iwasawaSourceIndexEquiv
  change (if hij' : i < j then
      Sum.inr (Sum.inr (⟨(i, j), hij'⟩ : nnIndex n))
    else if hji : j < i then
      Sum.inl (⟨(j, i), hji⟩ : nnIndex n)
    else
      Sum.inr (Sum.inl i)) =
      Sum.inr (Sum.inr (⟨(i, j), hij⟩ : nnIndex n))
  rw [dif_pos hij]

lemma iwasawaSourceBasis_apply_lower {i j : Fin n} (hji : j < i) :
    iwasawaSourceBasis (n := n) (i, j) =
      (skBasis (⟨(j, i), hji⟩ : nnIndex n), (0, 0)) := by
  rw [iwasawaSourceBasis, Module.Basis.reindex_apply,
    iwasawaSourceIndexEquiv_symm_lower hji, iwasawaSourceBasisProd,
    Module.Basis.prod_apply]
  rfl

lemma iwasawaSourceBasis_apply_diag (i : Fin n) :
    iwasawaSourceBasis (n := n) (i, i) =
      (0, ((Pi.basisFun ℝ (Fin n)) i, 0)) := by
  rw [iwasawaSourceBasis, Module.Basis.reindex_apply,
    iwasawaSourceIndexEquiv_symm_diag, iwasawaSourceBasisProd,
    Module.Basis.prod_apply]
  change (0, ((Pi.basisFun ℝ (Fin n)).prod nnBasis) (Sum.inl i)) =
    (0, ((Pi.basisFun ℝ (Fin n)) i, 0))
  rw [Module.Basis.prod_apply]
  rfl

lemma iwasawaSourceBasis_apply_upper {i j : Fin n} (hij : i < j) :
    iwasawaSourceBasis (n := n) (i, j) =
      (0, (0, nnBasisVec (⟨(i, j), hij⟩ : nnIndex n))) := by
  rw [iwasawaSourceBasis, Module.Basis.reindex_apply,
    iwasawaSourceIndexEquiv_symm_upper hij, iwasawaSourceBasisProd,
    Module.Basis.prod_apply]
  change (0, ((Pi.basisFun ℝ (Fin n)).prod nnBasis)
      (Sum.inr (⟨(i, j), hij⟩ : nnIndex n))) =
    (0, (0, nnBasisVec (⟨(i, j), hij⟩ : nnIndex n)))
  rw [Module.Basis.prod_apply]
  simp

/-! ## Determinant in Iwasawa source and matrix-entry bases -/

noncomputable def detInIwasawaBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (LinearMap.toMatrix (iwasawaSourceBasis (n := n))
    (Matrix.stdBasis ℝ (Fin n) (Fin n)) L.toLinearMap).det

@[simp] lemma detInIwasawaBases_def
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    detInIwasawaBases L =
      (LinearMap.toMatrix (iwasawaSourceBasis (n := n))
        (Matrix.stdBasis ℝ (Fin n) (Fin n)) L.toLinearMap).det := rfl

noncomputable def absDetInIwasawaBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  |detInIwasawaBases L|

@[simp] lemma absDetInIwasawaBases_def
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    absDetInIwasawaBases L = |detInIwasawaBases L| := rfl

/-! ## Normalized derivative entries in the Iwasawa bases

At `(1, a, 1)`, the actual derivative has a block-triangular shape in
the source basis above and the matrix-entry target basis. The following
entry lemmas record the diagonal entries and the one skew off-block term
needed for the eventual determinant computation. -/

lemma posDiag_mul_entry_left (a : A n) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (a.1 * M) i j = a.1 i i * M i j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i
    (fun b _ hb => by rw [a.2.1 i b (Ne.symm hb), zero_mul])
    (fun hi => by exact False.elim (hi (Finset.mem_univ i)))]

lemma posDiag_mul_entry_right (M : Matrix (Fin n) (Fin n) ℝ) (a : A n)
    (i j : Fin n) :
    (M * a.1) i j = M i j * a.1 j j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j
    (fun b _ hb => by rw [a.2.1 b j hb, mul_zero])
    (fun hj => by exact False.elim (hj (Finset.mem_univ j)))]

lemma iwasawaMatrixLeibnizCLM_one_a_one_apply (a : A n)
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (X, v, Z) =
      (-(2 : ℝ)) • (X.1 * a.1) + a.1 * Matrix.diagonal v + a.1 * Z.1 := by
  simp

lemma iwasawaMatrixLeibnizCLM_one_a_one_entry_lower (a : A n)
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) {i j : Fin n} (hji : j < i) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (X, v, Z)) i j =
      (-(2 : ℝ)) * (X.1 i j * a.1 j j) := by
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [posDiag_mul_entry_right]
  rw [posDiag_mul_entry_left a (Matrix.diagonal v) i j]
  rw [posDiag_mul_entry_left a Z.1 i j]
  have hne : i ≠ j := ne_of_gt hji
  rw [Matrix.diagonal_apply_ne _ hne, Z.2 i j (le_of_lt hji)]
  ring

lemma iwasawaMatrixLeibnizCLM_one_a_one_entry_diag (a : A n)
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) (i : Fin n) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (X, v, Z)) i i =
      a.1 i i * v i := by
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [posDiag_mul_entry_right, sk_mem_apply_diag, zero_mul]
  rw [posDiag_mul_entry_left a (Matrix.diagonal v) i i]
  rw [posDiag_mul_entry_left a Z.1 i i]
  rw [Matrix.diagonal_apply_eq, Z.2 i i le_rfl]
  ring

lemma iwasawaMatrixLeibnizCLM_one_a_one_entry_upper (a : A n)
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) {i j : Fin n} (hij : i < j) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (X, v, Z)) i j =
      (-(2 : ℝ)) * (X.1 i j * a.1 j j) + a.1 i i * Z.1 i j := by
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [posDiag_mul_entry_right]
  rw [posDiag_mul_entry_left a (Matrix.diagonal v) i j]
  rw [posDiag_mul_entry_left a Z.1 i j]
  have hne : i ≠ j := ne_of_lt hij
  rw [Matrix.diagonal_apply_ne _ hne]
  ring

lemma iwasawaMatrixLeibnizCLM_one_a_one_source_lower_lower_entry
    (a : A n) {i j : Fin n} (hji : j < i) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (iwasawaSourceBasis (n := n) (i, j))) i j =
      2 * a.1 j j := by
  rw [iwasawaSourceBasis_apply_lower hji]
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [AddSubmonoid.coe_zero, Matrix.add_apply, Matrix.smul_apply]
  rw [posDiag_mul_entry_right]
  have hsk :
      (skBasis (⟨(j, i), hji⟩ : nnIndex n) : Matrix (Fin n) (Fin n) ℝ) i j =
        -1 := by
    simpa using skBasis_apply_lower (n := n) (⟨(j, i), hji⟩ : nnIndex n)
  rw [hsk]
  have hne : i ≠ j := ne_of_gt hji
  rw [posDiag_mul_entry_left, Matrix.diagonal_apply_ne _ hne, mul_zero]
  simp

lemma iwasawaMatrixLeibnizCLM_one_a_one_source_lower_upper_entry
    (a : A n) {i j : Fin n} (hji : j < i) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (iwasawaSourceBasis (n := n) (i, j))) j i =
      -(2 : ℝ) * a.1 i i := by
  rw [iwasawaSourceBasis_apply_lower hji]
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [AddSubmonoid.coe_zero, Matrix.add_apply, Matrix.smul_apply]
  rw [posDiag_mul_entry_right]
  have hsk :
      (skBasis (⟨(j, i), hji⟩ : nnIndex n) : Matrix (Fin n) (Fin n) ℝ) j i =
        1 := by
    simpa using skBasis_apply_upper (n := n) (⟨(j, i), hji⟩ : nnIndex n)
  rw [hsk]
  have hne : j ≠ i := ne_of_lt hji
  rw [posDiag_mul_entry_left, Matrix.diagonal_apply_ne _ hne, mul_zero]
  simp

lemma iwasawaMatrixLeibnizCLM_one_a_one_source_diag_diag_entry
    (a : A n) (i : Fin n) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (iwasawaSourceBasis (n := n) (i, i))) i i =
      a.1 i i := by
  rw [iwasawaSourceBasis_apply_diag]
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [AddSubmonoid.coe_zero, Matrix.add_apply, Matrix.smul_apply]
  rw [posDiag_mul_entry_left]
  simp [Matrix.diagonal_apply_eq, Pi.basisFun_apply, Pi.single_eq_same]

lemma iwasawaMatrixLeibnizCLM_one_a_one_source_upper_upper_entry
    (a : A n) {i j : Fin n} (hij : i < j) :
    (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (iwasawaSourceBasis (n := n) (i, j))) i j =
      a.1 i i := by
  rw [iwasawaSourceBasis_apply_upper hij]
  rw [iwasawaMatrixLeibnizCLM_one_a_one_apply]
  simp only [AddSubmonoid.coe_zero, Matrix.add_apply, Matrix.smul_apply]
  have hnn :
      (nnBasisVec (⟨(i, j), hij⟩ : nnIndex n) :
        Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
    simp [nnBasisVec]
  have hne : i ≠ j := ne_of_lt hij
  simp [posDiag_mul_entry_left, hnn, Matrix.diagonal_apply_ne _ hne]

@[simp] lemma matrixStdBasis_repr_apply
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ((Matrix.stdBasis ℝ (Fin n) (Fin n)).repr M) (i, j) = M i j := by
  simp [Matrix.stdBasis]

lemma iwasawaMatrixLeibnizCLM_one_a_one_toMatrix_lower_diag_entry
    (a : A n) {i j : Fin n} (hji : j < i) :
    (LinearMap.toMatrix (iwasawaSourceBasis (n := n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a
        (⟨1, IsUpperUnipotent.one⟩ : UU n)).toLinearMap)
        (i, j) (i, j) =
      2 * a.1 j j := by
  rw [LinearMap.toMatrix_apply]
  simp [iwasawaMatrixLeibnizCLM_one_a_one_source_lower_lower_entry, hji]

lemma iwasawaMatrixLeibnizCLM_one_a_one_toMatrix_lower_upper_entry
    (a : A n) {i j : Fin n} (hji : j < i) :
    (LinearMap.toMatrix (iwasawaSourceBasis (n := n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a
        (⟨1, IsUpperUnipotent.one⟩ : UU n)).toLinearMap)
        (j, i) (i, j) =
      -(2 : ℝ) * a.1 i i := by
  rw [LinearMap.toMatrix_apply]
  simp [iwasawaMatrixLeibnizCLM_one_a_one_source_lower_upper_entry, hji]

lemma iwasawaMatrixLeibnizCLM_one_a_one_toMatrix_diag_diag_entry
    (a : A n) (i : Fin n) :
    (LinearMap.toMatrix (iwasawaSourceBasis (n := n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a
        (⟨1, IsUpperUnipotent.one⟩ : UU n)).toLinearMap)
        (i, i) (i, i) =
      a.1 i i := by
  rw [LinearMap.toMatrix_apply]
  simp [iwasawaMatrixLeibnizCLM_one_a_one_source_diag_diag_entry]

lemma iwasawaMatrixLeibnizCLM_one_a_one_toMatrix_upper_diag_entry
    (a : A n) {i j : Fin n} (hij : i < j) :
    (LinearMap.toMatrix (iwasawaSourceBasis (n := n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a
        (⟨1, IsUpperUnipotent.one⟩ : UU n)).toLinearMap)
        (i, j) (i, j) =
      a.1 i i := by
  rw [LinearMap.toMatrix_apply]
  simp [iwasawaMatrixLeibnizCLM_one_a_one_source_upper_upper_entry, hij]

noncomputable def iwasawaSourceTargetLinearEquiv :
    ((Sk n) × ((Fin n → ℝ) × (NN n))) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (iwasawaSourceBasis (n := n)).equiv
    (Matrix.stdBasis ℝ (Fin n) (Fin n)) (Equiv.refl _)

lemma iwasawaSourceTargetLinearEquiv_symm_repr
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    (iwasawaSourceBasis (n := n)).repr
        ((iwasawaSourceTargetLinearEquiv (n := n)).symm Y) =
      (Matrix.stdBasis ℝ (Fin n) (Fin n)).repr Y := by
  simp [iwasawaSourceTargetLinearEquiv, Module.Basis.equiv]

lemma toMatrix_comp_iwasawaSourceTargetLinearEquiv_symm
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.toMatrix (iwasawaSourceBasis (n := n)) (iwasawaSourceBasis (n := n))
      ((iwasawaSourceTargetLinearEquiv (n := n)).symm.toLinearMap.comp L.toLinearMap) =
    LinearMap.toMatrix (iwasawaSourceBasis (n := n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n)) L.toLinearMap := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simpa using congrArg (fun f : (Fin n × Fin n) →₀ ℝ => f i)
    (iwasawaSourceTargetLinearEquiv_symm_repr (n := n)
      (L (iwasawaSourceBasis (n := n) j)))

theorem iwasawaMatrixLeibnizCLM_one_a_one_map_eq_zero_iff (a : A n)
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (X, v, Z) = 0 ↔
      X = 0 ∧ v = 0 ∧ Z = 0 := by
  constructor
  · intro hzero
    have hXzero : X = 0 := by
      apply Subtype.ext
      ext i j
      rcases lt_trichotomy i j with hij | hEq | hji
      · have hentry :
            (iwasawaMatrixLeibnizCLM
              (⟨1, IsOrthogonal.one⟩ : K n) a
              (⟨1, IsUpperUnipotent.one⟩ : UU n) (X, v, Z)) j i = 0 := by
          simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) hzero
        rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_lower a X v Z hij] at hentry
        have hprod : X.1 j i * a.1 i i = 0 :=
          (mul_eq_zero.mp hentry).resolve_left (by norm_num)
        have hxji : X.1 j i = 0 :=
          (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (a.2.2 i))
        have hswap := sk_mem_apply_swap X j i
        rw [hswap, hxji, neg_zero]
        simp
      · subst hEq
        simp
      · have hentry :
            (iwasawaMatrixLeibnizCLM
              (⟨1, IsOrthogonal.one⟩ : K n) a
              (⟨1, IsUpperUnipotent.one⟩ : UU n) (X, v, Z)) i j = 0 := by
          simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hzero
        rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_lower a X v Z hji] at hentry
        have hprod : X.1 i j * a.1 j j = 0 :=
          (mul_eq_zero.mp hentry).resolve_left (by norm_num)
        exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (a.2.2 j))
    have hvzero : v = 0 := by
      funext i
      have hentry :
          (iwasawaMatrixLeibnizCLM
            (⟨1, IsOrthogonal.one⟩ : K n) a
            (⟨1, IsUpperUnipotent.one⟩ : UU n) (X, v, Z)) i i = 0 := by
        simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hzero
      rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_diag a X v Z i] at hentry
      exact (mul_eq_zero.mp hentry).resolve_left (ne_of_gt (a.2.2 i))
    have hZzero : Z = 0 := by
      apply Subtype.ext
      ext i j
      by_cases hle : j ≤ i
      · exact Z.2 i j hle
      · have hij : i < j := lt_of_not_ge hle
        have hentry :
            (iwasawaMatrixLeibnizCLM
              (⟨1, IsOrthogonal.one⟩ : K n) a
              (⟨1, IsUpperUnipotent.one⟩ : UU n) (X, v, Z)) i j = 0 := by
          simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hzero
        rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_upper a X v Z hij] at hentry
        rw [hXzero] at hentry
        simp at hentry
        exact hentry.resolve_left (ne_of_gt (a.2.2 i))
    exact ⟨hXzero, hvzero, hZzero⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem iwasawaMatrixLeibnizCLM_one_a_one_injective (a : A n) :
    Function.Injective (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) := by
  intro p q hpq
  let L := iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
  have hzero : L (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hz := (iwasawaMatrixLeibnizCLM_one_a_one_map_eq_zero_iff
      a (p - q).1 (p - q).2.1 (p - q).2.2).mp (by
    simpa only [Prod.eta] using hzero)
  apply Prod.ext
  · exact sub_eq_zero.mp hz.1
  · apply Prod.ext
    · exact sub_eq_zero.mp hz.2.1
    · exact sub_eq_zero.mp hz.2.2

theorem detInIwasawaBases_one_a_one_ne_zero (a : A n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) ≠ 0 := by
  let L := iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
  let E := iwasawaSourceTargetLinearEquiv (n := n)
  let F : (Sk n) × ((Fin n → ℝ) × (NN n)) →ₗ[ℝ]
      (Sk n) × ((Fin n → ℝ) × (NN n)) := E.symm.toLinearMap.comp L.toLinearMap
  have hmat :
      LinearMap.toMatrix (iwasawaSourceBasis (n := n)) (iwasawaSourceBasis (n := n)) F =
        LinearMap.toMatrix (iwasawaSourceBasis (n := n))
          (Matrix.stdBasis ℝ (Fin n) (Fin n)) L.toLinearMap := by
    simpa [F, E, L] using toMatrix_comp_iwasawaSourceTargetLinearEquiv_symm (n := n) L
  have hdet_eq : detInIwasawaBases L = LinearMap.det F := by
    rw [detInIwasawaBases, ← hmat, LinearMap.det_toMatrix]
  rw [hdet_eq]
  have hFinj : Function.Injective F := by
    intro x y hxy
    dsimp [F] at hxy
    apply iwasawaMatrixLeibnizCLM_one_a_one_injective (n := n) a
    exact E.symm.injective hxy
  have hker : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot_of_injective hFinj
  intro hdet
  have hker_ne : LinearMap.ker F ≠ ⊥ := (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
  exact hker_ne hker

/-! ## Block-ordered determinant for the normalized derivative

The matrix-position basis above is natural but not ordered by the three
Iwasawa blocks.  For the explicit determinant, we keep the same source
vectors and target matrix-entry vectors, but index them as
`lower ⊕ (diagonal ⊕ upper)`.  The block-level map below reverses this
order (`upper = 0`, `diagonal = 1`, `lower = 2`) so that mathlib's
`BlockTriangular` determinant lemma applies directly. -/

abbrev iwasawaBlockIndex (n : ℕ) : Type :=
  (nnIndex n) ⊕ ((Fin n) ⊕ (nnIndex n))

noncomputable def iwasawaBlockSourceBasis :
    Basis (iwasawaBlockIndex n) ℝ ((Sk n) × ((Fin n → ℝ) × (NN n))) :=
  iwasawaSourceBasisProd

@[simp] lemma iwasawaBlockSourceBasis_apply_lower (ij : nnIndex n) :
    iwasawaBlockSourceBasis (n := n) (Sum.inl ij) =
      (skBasis ij, (0, 0)) := by
  rw [iwasawaBlockSourceBasis, iwasawaSourceBasisProd, Module.Basis.prod_apply]
  rfl

@[simp] lemma iwasawaBlockSourceBasis_apply_diag (i : Fin n) :
    iwasawaBlockSourceBasis (n := n) (Sum.inr (Sum.inl i)) =
      (0, ((Pi.basisFun ℝ (Fin n)) i, 0)) := by
  rw [iwasawaBlockSourceBasis, iwasawaSourceBasisProd, Module.Basis.prod_apply]
  change (0, ((Pi.basisFun ℝ (Fin n)).prod nnBasis) (Sum.inl i)) =
    (0, ((Pi.basisFun ℝ (Fin n)) i, 0))
  rw [Module.Basis.prod_apply]
  rfl

@[simp] lemma iwasawaBlockSourceBasis_apply_upper (ij : nnIndex n) :
    iwasawaBlockSourceBasis (n := n) (Sum.inr (Sum.inr ij)) =
      (0, (0, nnBasisVec ij)) := by
  rw [iwasawaBlockSourceBasis, iwasawaSourceBasisProd, Module.Basis.prod_apply]
  change (0, ((Pi.basisFun ℝ (Fin n)).prod nnBasis) (Sum.inr ij)) =
    (0, (0, nnBasisVec ij))
  rw [Module.Basis.prod_apply]
  simp

noncomputable def iwasawaBlockTargetBasis :
    Basis (iwasawaBlockIndex n) ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.stdBasis ℝ (Fin n) (Fin n)).reindex
    (iwasawaSourceIndexEquiv (n := n)).symm

@[simp] lemma iwasawaBlockTargetBasis_repr_apply
    (M : Matrix (Fin n) (Fin n) ℝ) (s : iwasawaBlockIndex n) :
    ((iwasawaBlockTargetBasis (n := n)).repr M) s =
      M ((iwasawaSourceIndexEquiv (n := n)) s).1
        ((iwasawaSourceIndexEquiv (n := n)) s).2 := by
  rw [iwasawaBlockTargetBasis, Module.Basis.repr_reindex_apply]
  exact matrixStdBasis_repr_apply M _ _

noncomputable def detInIwasawaBlockBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (LinearMap.toMatrix (iwasawaBlockSourceBasis (n := n))
    (iwasawaBlockTargetBasis (n := n)) L.toLinearMap).det

@[simp] lemma detInIwasawaBlockBases_def
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    detInIwasawaBlockBases L =
      (LinearMap.toMatrix (iwasawaBlockSourceBasis (n := n))
        (iwasawaBlockTargetBasis (n := n)) L.toLinearMap).det := rfl

noncomputable def absDetInIwasawaBlockBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  |detInIwasawaBlockBases L|

@[simp] lemma absDetInIwasawaBlockBases_def
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    absDetInIwasawaBlockBases L = |detInIwasawaBlockBases L| := rfl

def iwasawaBlockLevel : iwasawaBlockIndex n → Fin 3
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 0

noncomputable def iwasawaBlockMatrixOne (a : A n) :
    Matrix (iwasawaBlockIndex n) (iwasawaBlockIndex n) ℝ :=
  LinearMap.toMatrix (iwasawaBlockSourceBasis (n := n))
    (iwasawaBlockTargetBasis (n := n))
    (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a
      (⟨1, IsUpperUnipotent.one⟩ : UU n)).toLinearMap

lemma iwasawaBlockMatrixOne_lower_lower
    (a : A n) (row col : nnIndex n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inl row) (Sum.inl col) =
      if row = col then 2 * a.1 row.1.1 row.1.1 else 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_lower, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (skBasis col, (0, 0))) row.1.2 row.1.1 =
      if row = col then 2 * a.1 row.1.1 row.1.1 else 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_lower a (skBasis col) 0 0 row.2]
  rw [skBasis_apply_lower_index row col]
  by_cases h : row = col
  · subst h
    simp
  · simp [h]

lemma iwasawaBlockMatrixOne_lower_diag
    (a : A n) (row : nnIndex n) (col : Fin n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inl row) (Sum.inr (Sum.inl col)) = 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_diag, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (0, ((Pi.basisFun ℝ (Fin n)) col, 0))) row.1.2 row.1.1 = 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_lower a 0 ((Pi.basisFun ℝ (Fin n)) col) 0 row.2]
  simp

lemma iwasawaBlockMatrixOne_lower_upper
    (a : A n) (row col : nnIndex n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inl row) (Sum.inr (Sum.inr col)) = 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_upper, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (0, (0, nnBasisVec col))) row.1.2 row.1.1 = 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_lower a 0 0 (nnBasisVec col) row.2]
  simp

lemma iwasawaBlockMatrixOne_diag_lower
    (a : A n) (row : Fin n) (col : nnIndex n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inr (Sum.inl row)) (Sum.inl col) = 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_lower, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (skBasis col, (0, 0))) row row = 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_diag a (skBasis col) 0 0 row]
  simp

lemma iwasawaBlockMatrixOne_diag_diag
    (a : A n) (row col : Fin n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inl col)) =
      if row = col then a.1 row row else 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_diag, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (0, ((Pi.basisFun ℝ (Fin n)) col, 0))) row row =
      if row = col then a.1 row row else 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_diag a 0 ((Pi.basisFun ℝ (Fin n)) col) 0 row]
  by_cases h : row = col
  · subst h
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h]

lemma iwasawaBlockMatrixOne_diag_upper
    (a : A n) (row : Fin n) (col : nnIndex n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inr col)) = 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_upper, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (0, (0, nnBasisVec col))) row row = 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_diag a 0 0 (nnBasisVec col) row]
  simp

lemma iwasawaBlockMatrixOne_upper_lower
    (a : A n) (row col : nnIndex n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inr (Sum.inr row)) (Sum.inl col) =
      if row = col then -(2 : ℝ) * a.1 row.1.2 row.1.2 else 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_lower, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (skBasis col, (0, 0))) row.1.1 row.1.2 =
      if row = col then -(2 : ℝ) * a.1 row.1.2 row.1.2 else 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_upper a (skBasis col) 0 0 row.2]
  rw [skBasis_apply_upper_index row col]
  by_cases h : row = col
  · subst h
    simp
  · simp [h]

lemma iwasawaBlockMatrixOne_upper_diag
    (a : A n) (row : nnIndex n) (col : Fin n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inr (Sum.inr row)) (Sum.inr (Sum.inl col)) = 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_diag, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (0, ((Pi.basisFun ℝ (Fin n)) col, 0))) row.1.1 row.1.2 = 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_upper a 0 ((Pi.basisFun ℝ (Fin n)) col) 0 row.2]
  simp

lemma iwasawaBlockMatrixOne_upper_upper
    (a : A n) (row col : nnIndex n) :
    iwasawaBlockMatrixOne (n := n) a (Sum.inr (Sum.inr row)) (Sum.inr (Sum.inr col)) =
      if row = col then a.1 row.1.1 row.1.1 else 0 := by
  rw [iwasawaBlockMatrixOne, LinearMap.toMatrix_apply]
  rw [iwasawaBlockSourceBasis_apply_upper, iwasawaBlockTargetBasis_repr_apply]
  change (iwasawaMatrixLeibnizCLM
        (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
        (0, (0, nnBasisVec col))) row.1.1 row.1.2 =
      if row = col then a.1 row.1.1 row.1.1 else 0
  rw [iwasawaMatrixLeibnizCLM_one_a_one_entry_upper a 0 0 (nnBasisVec col) row.2]
  rw [nnBasisVec_apply_upper_index row col]
  by_cases h : row = col
  · subst h
    simp
  · simp [h]

theorem iwasawaMatrixLeibnizCLM_one_a_one_blockTriangular (a : A n) :
    (iwasawaBlockMatrixOne (n := n) a).BlockTriangular (iwasawaBlockLevel (n := n)) := by
  intro row col hcolrow
  rcases row with row | (row | row) <;> rcases col with col | (col | col)
  · exfalso
    norm_num [iwasawaBlockLevel] at hcolrow
  · exact iwasawaBlockMatrixOne_lower_diag (n := n) a row col
  · exact iwasawaBlockMatrixOne_lower_upper (n := n) a row col
  · exfalso
    norm_num [iwasawaBlockLevel] at hcolrow
    have hv := congrArg Fin.val hcolrow
    norm_num at hv
  · exfalso
    norm_num [iwasawaBlockLevel] at hcolrow
  · exact iwasawaBlockMatrixOne_diag_upper (n := n) a row col
  · exfalso
    norm_num [iwasawaBlockLevel] at hcolrow
  · exfalso
    norm_num [iwasawaBlockLevel] at hcolrow
  · exfalso
    norm_num [iwasawaBlockLevel] at hcolrow

def iwasawaBlockUpperEquiv :
    {s : iwasawaBlockIndex n // iwasawaBlockLevel (n := n) s = 0} ≃ nnIndex n where
  toFun s := by
    rcases s with ⟨s, hs⟩
    rcases s with ij | (i | ij)
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · exact ij
  invFun ij := ⟨Sum.inr (Sum.inr ij), rfl⟩
  left_inv := by
    rintro ⟨s, hs⟩
    rcases s with ij | (i | ij)
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · rfl
  right_inv := by
    intro ij
    rfl

def iwasawaBlockDiagEquiv :
    {s : iwasawaBlockIndex n // iwasawaBlockLevel (n := n) s = 1} ≃ Fin n where
  toFun s := by
    rcases s with ⟨s, hs⟩
    rcases s with ij | (i | ij)
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · exact i
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
  invFun i := ⟨Sum.inr (Sum.inl i), rfl⟩
  left_inv := by
    rintro ⟨s, hs⟩
    rcases s with ij | (i | ij)
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · rfl
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
  right_inv := by
    intro i
    rfl

def iwasawaBlockLowerEquiv :
    {s : iwasawaBlockIndex n // iwasawaBlockLevel (n := n) s = 2} ≃ nnIndex n where
  toFun s := by
    rcases s with ⟨s, hs⟩
    rcases s with ij | (i | ij)
    · exact ij
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
  invFun ij := ⟨Sum.inl ij, rfl⟩
  left_inv := by
    rintro ⟨s, hs⟩
    rcases s with ij | (i | ij)
    · rfl
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
    · exfalso
      have hv := congrArg Fin.val hs
      norm_num [iwasawaBlockLevel] at hv
  right_inv := by
    intro ij
    rfl

lemma iwasawaBlockMatrixOne_upper_block_det (a : A n) :
    ((iwasawaBlockMatrixOne (n := n) a).toSquareBlock (iwasawaBlockLevel (n := n)) 0).det =
      ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 := by
  let B := (iwasawaBlockMatrixOne (n := n) a).toSquareBlock (iwasawaBlockLevel (n := n)) 0
  let e := (iwasawaBlockUpperEquiv (n := n)).symm
  have hsub :
      B.submatrix e e =
        Matrix.diagonal (fun ij : nnIndex n => a.1 ij.1.1 ij.1.1) := by
    ext row col
    change iwasawaBlockMatrixOne (n := n) a
        (Sum.inr (Sum.inr row)) (Sum.inr (Sum.inr col)) =
      Matrix.diagonal (fun ij : nnIndex n => a.1 ij.1.1 ij.1.1) row col
    rw [iwasawaBlockMatrixOne_upper_upper, Matrix.diagonal_apply]
  have hdet := Matrix.det_submatrix_equiv_self e B
  rw [hsub, Matrix.det_diagonal] at hdet
  exact hdet.symm

lemma iwasawaBlockMatrixOne_diag_block_det (a : A n) :
    ((iwasawaBlockMatrixOne (n := n) a).toSquareBlock (iwasawaBlockLevel (n := n)) 1).det =
      ∏ i : Fin n, a.1 i i := by
  let B := (iwasawaBlockMatrixOne (n := n) a).toSquareBlock (iwasawaBlockLevel (n := n)) 1
  let e := (iwasawaBlockDiagEquiv (n := n)).symm
  have hsub :
      B.submatrix e e =
        Matrix.diagonal (fun i : Fin n => a.1 i i) := by
    ext row col
    change iwasawaBlockMatrixOne (n := n) a
        (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inl col)) =
      Matrix.diagonal (fun i : Fin n => a.1 i i) row col
    rw [iwasawaBlockMatrixOne_diag_diag, Matrix.diagonal_apply]
  have hdet := Matrix.det_submatrix_equiv_self e B
  rw [hsub, Matrix.det_diagonal] at hdet
  exact hdet.symm

lemma iwasawaBlockMatrixOne_lower_block_det (a : A n) :
    ((iwasawaBlockMatrixOne (n := n) a).toSquareBlock (iwasawaBlockLevel (n := n)) 2).det =
      ∏ ij : nnIndex n, 2 * a.1 ij.1.1 ij.1.1 := by
  let B := (iwasawaBlockMatrixOne (n := n) a).toSquareBlock (iwasawaBlockLevel (n := n)) 2
  let e := (iwasawaBlockLowerEquiv (n := n)).symm
  have hsub :
      B.submatrix e e =
        Matrix.diagonal (fun ij : nnIndex n => 2 * a.1 ij.1.1 ij.1.1) := by
    ext row col
    change iwasawaBlockMatrixOne (n := n) a
        (Sum.inl row) (Sum.inl col) =
      Matrix.diagonal (fun ij : nnIndex n => 2 * a.1 ij.1.1 ij.1.1) row col
    rw [iwasawaBlockMatrixOne_lower_lower, Matrix.diagonal_apply]
  have hdet := Matrix.det_submatrix_equiv_self e B
  rw [hsub, Matrix.det_diagonal] at hdet
  exact hdet.symm

theorem detInIwasawaBlockBases_one_a_one_eq_prod (a : A n) :
    detInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) *
        (∏ i : Fin n, a.1 i i) *
          (∏ ij : nnIndex n, 2 * a.1 ij.1.1 ij.1.1) := by
  change (iwasawaBlockMatrixOne (n := n) a).det =
      (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) *
        (∏ i : Fin n, a.1 i i) *
          (∏ ij : nnIndex n, 2 * a.1 ij.1.1 ij.1.1)
  rw [(iwasawaMatrixLeibnizCLM_one_a_one_blockTriangular (n := n) a).det_fintype]
  rw [Fin.prod_univ_three]
  rw [iwasawaBlockMatrixOne_upper_block_det,
    iwasawaBlockMatrixOne_diag_block_det, iwasawaBlockMatrixOne_lower_block_det]

theorem absDetInIwasawaBlockBases_one_a_one_eq_abs_prod (a : A n) :
    absDetInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      |(∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) *
        (∏ i : Fin n, a.1 i i) *
          (∏ ij : nnIndex n, 2 * a.1 ij.1.1 ij.1.1)| := by
  rw [absDetInIwasawaBlockBases, detInIwasawaBlockBases_one_a_one_eq_prod]

theorem absDetInIwasawaBlockBases_one_a_one_eq_prod (a : A n) :
    absDetInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) *
        (∏ i : Fin n, a.1 i i) *
          (∏ ij : nnIndex n, 2 * a.1 ij.1.1 ij.1.1) := by
  rw [absDetInIwasawaBlockBases, detInIwasawaBlockBases_one_a_one_eq_prod]
  have hupper : 0 < ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 :=
    Finset.prod_pos (fun ij _ => a.2.2 ij.1.1)
  have hdiag : 0 < ∏ i : Fin n, a.1 i i :=
    Finset.prod_pos (fun i _ => a.2.2 i)
  have hlower : 0 < ∏ ij : nnIndex n, 2 * a.1 ij.1.1 ij.1.1 :=
    Finset.prod_pos (fun ij _ => mul_pos (by norm_num) (a.2.2 ij.1.1))
  exact abs_of_pos (mul_pos (mul_pos hupper hdiag) hlower)

theorem detInIwasawaBlockBases_one_a_one_eq_scaled_prod (a : A n) :
    detInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 *
          (∏ i : Fin n, a.1 i i) := by
  rw [detInIwasawaBlockBases_one_a_one_eq_prod]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

theorem absDetInIwasawaBlockBases_one_a_one_eq_scaled_prod (a : A n) :
    absDetInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 *
          (∏ i : Fin n, a.1 i i) := by
  rw [absDetInIwasawaBlockBases_one_a_one_eq_prod]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

theorem detInIwasawaBases_eq_detInIwasawaBlockBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    detInIwasawaBases L = detInIwasawaBlockBases L := by
  let e := iwasawaSourceIndexEquiv (n := n)
  let M := LinearMap.toMatrix (iwasawaBlockSourceBasis (n := n))
    (iwasawaBlockTargetBasis (n := n)) L.toLinearMap
  have hmat :
      LinearMap.toMatrix (iwasawaSourceBasis (n := n))
        (Matrix.stdBasis ℝ (Fin n) (Fin n)) L.toLinearMap =
        M.submatrix e.symm e.symm := by
    ext p q
    rw [LinearMap.toMatrix_apply]
    change ((Matrix.stdBasis ℝ (Fin n) (Fin n)).repr (L (iwasawaSourceBasis (n := n) q))) p =
      M (e.symm p) (e.symm q)
    rw [matrixStdBasis_repr_apply]
    dsimp [M]
    rw [LinearMap.toMatrix_apply, iwasawaBlockTargetBasis_repr_apply]
    have hsource :
        iwasawaBlockSourceBasis (n := n) (e.symm q) =
          iwasawaSourceBasis (n := n) q := by
      rw [iwasawaSourceBasis, iwasawaBlockSourceBasis, Module.Basis.reindex_apply]
    rw [hsource]
    simp [e]
  rw [detInIwasawaBases, detInIwasawaBlockBases, hmat]
  exact Matrix.det_submatrix_equiv_self e.symm M

theorem absDetInIwasawaBases_eq_absDetInIwasawaBlockBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ) :
    absDetInIwasawaBases L = absDetInIwasawaBlockBases L := by
  rw [absDetInIwasawaBases, absDetInIwasawaBlockBases,
    detInIwasawaBases_eq_detInIwasawaBlockBases]

theorem detInIwasawaBases_one_a_one_eq_scaled_prod (a : A n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 *
          (∏ i : Fin n, a.1 i i) := by
  rw [detInIwasawaBases_eq_detInIwasawaBlockBases,
    detInIwasawaBlockBases_one_a_one_eq_scaled_prod]

theorem absDetInIwasawaBases_one_a_one_eq_scaled_prod (a : A n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 *
          (∏ i : Fin n, a.1 i i) := by
  rw [absDetInIwasawaBases_eq_absDetInIwasawaBlockBases,
    absDetInIwasawaBlockBases_one_a_one_eq_scaled_prod]

lemma posDiag_det_eq_prod_diag (a : A n) :
    a.1.det = ∏ i : Fin n, a.1 i i := by
  have hdiag : a.1 = Matrix.diagonal (fun i : Fin n => a.1 i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [a.2.1 i j h]
      simp [Matrix.diagonal_apply, h]
  calc
    a.1.det = (Matrix.diagonal (fun i : Fin n => a.1 i i)).det := by
      exact congrArg Matrix.det hdiag
    _ = ∏ i : Fin n, a.1 i i := by
      rw [Matrix.det_diagonal]

theorem detInIwasawaBases_one_a_one_eq_scaled_upper_sq_mul_det (a : A n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 *
          a.1.det := by
  rw [detInIwasawaBases_one_a_one_eq_scaled_prod, posDiag_det_eq_prod_diag]

theorem absDetInIwasawaBases_one_a_one_eq_scaled_upper_sq_mul_det (a : A n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 *
          a.1.det := by
  rw [absDetInIwasawaBases_one_a_one_eq_scaled_prod, posDiag_det_eq_prod_diag]

/- The conventional rewrite
`(∏_{i<j} a_i)^2 * det(a) = det(a)^n * det(adNN a)` is a finite
product-count identity over `Fin n`; it is proved below after the
explicit determinant formula for `adNN`. -/

/-! ## `adNN a` is diagonal on `nnBasis`

By `adNN_entry` (T1-4 L2), the (p, q) entry of `adNN a (nnBasisVec ij)`
equals `(a.1 p p / a.1 q q) * Matrix.single ij.1.1 ij.1.2 1 p q`. The
only nonzero entry is at `(p, q) = (ij.1.1, ij.1.2)`, with value
`a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2`. So `adNN a (nnBasisVec ij) =
(scalar) • nnBasisVec ij`. -/

theorem adNN_nnBasisVec (a : A n) (ij : nnIndex n) :
    adNN a (nnBasisVec ij) = (a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2) • nnBasisVec ij := by
  apply Subtype.ext
  ext p q
  -- LHS .val p q
  rw [adNN_entry, nnBasisVec_val]
  show (a.1 p p / a.1 q q) * Matrix.single ij.1.1 ij.1.2 (1 : ℝ) p q =
      ((a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2) • Matrix.single ij.1.1 ij.1.2 (1 : ℝ)) p q
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  by_cases h : ij.1.1 = p ∧ ij.1.2 = q
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [if_pos ⟨rfl, rfl⟩]
  · rw [if_neg h, mul_zero, mul_zero]

/-! ## Matrix of `adNN a` in `nnBasis` is diagonal -/

private lemma adNN_toMatrix_diagonal (a : A n) :
    LinearMap.toMatrix nnBasis nnBasis (adNN a).toLinearMap =
      Matrix.diagonal (fun ij : nnIndex n => a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2) := by
  ext kl ij
  simp only [LinearMap.toMatrix_apply, nnBasis_apply, ContinuousLinearMap.coe_coe,
             adNN_nnBasisVec, map_smul, Finsupp.smul_apply, smul_eq_mul,
             Matrix.diagonal_apply]
  rw [show nnBasisVec ij = nnBasis ij from (nnBasis_apply ij).symm]
  simp only [Module.Basis.repr_self_apply]
  -- LHS: scalar * (if ij = kl then 1 else 0). RHS: if kl = ij then scalar else 0.
  by_cases hkl : kl = ij
  · subst hkl; simp
  · rw [if_neg (Ne.symm hkl), if_neg hkl, mul_zero]

/-! ## T1-6 main theorem: explicit product formula -/

/-- **T1-6 explicit product formula (subtype-indexed).** The
determinant of `adNN a` equals the product over the strictly-upper-
triangular index pairs of the eigenvalue ratios. -/
theorem adNN_det_eq_pair_product (a : A n) :
    LinearMap.det (adNN a).toLinearMap =
      ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2 := by
  -- Use the chain: LinearMap.det f = Matrix.det (toMatrix b b f) (by `LinearMap.det_toMatrix`).
  -- Then adNN_toMatrix_diagonal replaces with `diagonal`. Then `Matrix.det_diagonal`.
  have h1 := (LinearMap.det_toMatrix nnBasis (adNN a).toLinearMap).symm
  rw [h1, adNN_toMatrix_diagonal, Matrix.det_diagonal]

/-! ## Product bridge to the conventional determinant formula

The determinant computation above gives the factor
`(∏_{i<j} a_i)^2 * det(a)`.  The lemmas in this section rewrite it as
`det(a)^n * det(adNN a)`, using the already established orientation
`det(adNN a) = ∏_{i<j} a_i / a_j`. -/

lemma nnIndex_snd_prod_mul_diag_prod_mul_fst_prod_eq_diag_prod_pow
    (d : Fin n → ℝ) :
    (∏ ij : nnIndex n, d ij.1.2) *
        ((∏ i : Fin n, d i) * (∏ ij : nnIndex n, d ij.1.1)) =
      (∏ i : Fin n, d i) ^ n := by
  have hfull_pow :
      (∏ p : Fin n × Fin n, d p.1) = (∏ i : Fin n, d i) ^ n := by
    rw [Fintype.prod_prod_type]
    simp [Finset.prod_const, Fintype.card_fin]
    rw [← Finset.prod_pow]
  have hfull_block :
      (∏ p : Fin n × Fin n, d p.1) =
        (∏ ij : nnIndex n, d ij.1.2) *
          ((∏ i : Fin n, d i) * (∏ ij : nnIndex n, d ij.1.1)) := by
    rw [← Equiv.prod_comp (iwasawaSourceIndexEquiv (n := n))
      (fun p : Fin n × Fin n => d p.1)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    rfl
  rw [← hfull_block]
  exact hfull_pow

lemma nnIndex_fst_prod_sq_mul_diag_prod_eq_diag_prod_pow_mul_ratio_prod
    (d : Fin n → ℝ) (hpos : ∀ i, 0 < d i) :
    (∏ ij : nnIndex n, d ij.1.1) ^ 2 * (∏ i : Fin n, d i) =
      (∏ i : Fin n, d i) ^ n *
        (∏ ij : nnIndex n, d ij.1.1 / d ij.1.2) := by
  let U : ℝ := ∏ ij : nnIndex n, d ij.1.1
  let V : ℝ := ∏ ij : nnIndex n, d ij.1.2
  let D : ℝ := ∏ i : Fin n, d i
  have hV : V ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos (fun ij _ => hpos ij.1.2))
  have hpart : V * (D * U) = D ^ n := by
    dsimp [U, V, D]
    exact nnIndex_snd_prod_mul_diag_prod_mul_fst_prod_eq_diag_prod_pow (n := n) d
  have hratio : (∏ ij : nnIndex n, d ij.1.1 / d ij.1.2) = U / V := by
    dsimp [U, V]
    rw [← Finset.prod_div_distrib]
  dsimp [U, V, D] at hV hpart hratio ⊢
  rw [hratio, ← hpart]
  field_simp [hV]

theorem nnIndex_diag_prod_sq_mul_det_eq_det_pow_mul_adNN_det (a : A n) :
    (∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1) ^ 2 * a.1.det =
      a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [posDiag_det_eq_prod_diag, adNN_det_eq_pair_product]
  exact nnIndex_fst_prod_sq_mul_diag_prod_eq_diag_prod_pow_mul_ratio_prod
    (n := n) (fun i : Fin n => a.1 i i) (fun i => a.2.2 i)

theorem detInIwasawaBlockBases_one_a_one_eq_scaled_det_pow_mul_det_adNN (a : A n) :
    detInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [detInIwasawaBlockBases_one_a_one_eq_scaled_prod]
  rw [mul_assoc]
  rw [nnIndex_fst_prod_sq_mul_diag_prod_eq_diag_prod_pow_mul_ratio_prod
    (n := n) (fun i : Fin n => a.1 i i) (fun i => a.2.2 i)]
  rw [← posDiag_det_eq_prod_diag a, ← adNN_det_eq_pair_product a]
  rw [← mul_assoc]

theorem absDetInIwasawaBlockBases_one_a_one_eq_scaled_det_pow_mul_det_adNN (a : A n) :
    absDetInIwasawaBlockBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [absDetInIwasawaBlockBases_one_a_one_eq_scaled_prod]
  rw [mul_assoc]
  rw [nnIndex_fst_prod_sq_mul_diag_prod_eq_diag_prod_pow_mul_ratio_prod
    (n := n) (fun i : Fin n => a.1 i i) (fun i => a.2.2 i)]
  rw [← posDiag_det_eq_prod_diag a, ← adNN_det_eq_pair_product a]
  rw [← mul_assoc]

theorem detInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN (a : A n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [detInIwasawaBases_one_a_one_eq_scaled_upper_sq_mul_det]
  rw [mul_assoc]
  rw [nnIndex_diag_prod_sq_mul_det_eq_det_pow_mul_adNN_det]
  rw [← mul_assoc]

theorem absDetInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN (a : A n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [absDetInIwasawaBases_one_a_one_eq_scaled_upper_sq_mul_det]
  rw [mul_assoc]
  rw [nnIndex_diag_prod_sq_mul_det_eq_det_pow_mul_adNN_det]
  rw [← mul_assoc]

/-! ## General factored-point transport

At a general Iwasawa point `(k, a, u)`, the derivative differs from the
normalized derivative at `(1, a, 1)` by a source transport
`(X, v, Z) ↦ (kᵀ X k, v, Z u⁻¹)` and a target transport `M ↦ k M u`.
The determinant statements below isolate these transport factors.  Proving
that their absolute determinants are `1` is the remaining linear-algebraic
step for the fully invariant arbitrary-point Jacobian formula. -/

noncomputable def skOrthConjLinearMap (k : K n) : Sk n →ₗ[ℝ] Sk n where
  toFun X := ⟨k.1.transpose * X.1 * k.1, by
    change (k.1.transpose * X.1 * k.1).transpose =
      -(k.1.transpose * X.1 * k.1)
    calc
      (k.1.transpose * X.1 * k.1).transpose =
          k.1.transpose * X.1.transpose * k.1 := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        simp [Matrix.mul_assoc]
      _ = k.1.transpose * (-X.1) * k.1 := by rw [X.2]
      _ = -(k.1.transpose * X.1 * k.1) := by simp [Matrix.mul_assoc]⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' c X := by
    apply Subtype.ext
    simp [Matrix.mul_assoc]

noncomputable def skOrthConjCLM (k : K n) : Sk n →L[ℝ] Sk n :=
  LinearMap.toContinuousLinearMap (skOrthConjLinearMap (n := n) k)

@[simp] lemma skOrthConjCLM_apply_val (k : K n) (X : Sk n) :
    ((skOrthConjCLM (n := n) k X : Sk n) :
        Matrix (Fin n) (Fin n) ℝ) =
      k.1.transpose * X.1 * k.1 := rfl

noncomputable def nnRightInvLinearMap (u : UU n) : NN n →ₗ[ℝ] NN n where
  toFun Z := ⟨Z.1 * u.1⁻¹, by
    intro i j hji
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hli : l ≤ i
    · rw [Z.2 i l hli, zero_mul]
    · have hil : i < l := lt_of_not_ge hli
      have hUpperInv : IsUpperTriangular u.1⁻¹ := (Iwasawa.IsUpperUnipotent.inv u.2).1
      have hjl : j < l := lt_of_le_of_lt hji hil
      rw [hUpperInv hjl, mul_zero]⟩
  map_add' Z W := by
    apply Subtype.ext
    simp [Matrix.add_mul]
  map_smul' c Z := by
    apply Subtype.ext
    simp

noncomputable def nnRightInvCLM (u : UU n) : NN n →L[ℝ] NN n :=
  LinearMap.toContinuousLinearMap (nnRightInvLinearMap (n := n) u)

@[simp] lemma nnRightInvCLM_apply_val (u : UU n) (Z : NN n) :
    ((nnRightInvCLM (n := n) u Z : NN n) :
        Matrix (Fin n) (Fin n) ℝ) =
      Z.1 * u.1⁻¹ := rfl

lemma nnRightInvCLM_toMatrix_entry (u : UU n) (row col : nnIndex n) :
    LinearMap.toMatrix nnBasis nnBasis (nnRightInvCLM (n := n) u).toLinearMap row col =
      if row.1.1 = col.1.1 then u.1⁻¹ col.1.2 row.1.2 else 0 := by
  rw [LinearMap.toMatrix_apply, nnBasis_repr_apply, nnBasis_apply]
  change (((nnRightInvCLM (n := n) u (nnBasisVec col) : NN n) :
      Matrix (Fin n) (Fin n) ℝ) row.1.1 row.1.2) =
    (if row.1.1 = col.1.1 then u.1⁻¹ col.1.2 row.1.2 else 0)
  rw [nnRightInvCLM_apply_val, nnBasisVec_val, Matrix.mul_apply]
  rw [Finset.sum_eq_single col.1.2]
  · simp only [Matrix.single_apply]
    by_cases hfirst : col.1.1 = row.1.1
    · simp [hfirst]
    · simp [hfirst, Ne.symm hfirst]
  · intro b _ hb
    rw [Matrix.single_apply]
    have hne : ¬ (col.1.1 = row.1.1 ∧ col.1.2 = b) := by
      rintro ⟨_, h2⟩
      exact hb h2.symm
    rw [if_neg hne, zero_mul]
  · intro hb
    simp at hb

lemma nnRightInvCLM_toMatrix_lowerTriangular (u : UU n) :
    letI : LinearOrder (nnIndex n) := nnIndexLexLinearOrder n
    (LinearMap.toMatrix nnBasis nnBasis (nnRightInvCLM (n := n) u).toLinearMap).BlockTriangular
      OrderDual.toDual := by
  letI : LinearOrder (nnIndex n) := nnIndexLexLinearOrder n
  intro row col hlt
  rw [nnRightInvCLM_toMatrix_entry]
  by_cases hfirst : row.1.1 = col.1.1
  · rw [if_pos hfirst]
    have hlex : (toLex (row.1.1, row.1.2) : Lex (Fin n × Fin n)) <
        toLex (col.1.1, col.1.2) := by
      exact hlt
    have hsecond : row.1.2 < col.1.2 := by
      rcases (Prod.Lex.toLex_lt_toLex.mp hlex) with hfirstlt | hsame
      · exact (hfirstlt.ne hfirst).elim
      · exact hsame.2
    have hUpperInv : IsUpperTriangular u.1⁻¹ := (Iwasawa.IsUpperUnipotent.inv u.2).1
    exact hUpperInv hsecond
  · rw [if_neg hfirst]

lemma nnRightInvCLM_toMatrix_diag (u : UU n) (ij : nnIndex n) :
    LinearMap.toMatrix nnBasis nnBasis (nnRightInvCLM (n := n) u).toLinearMap ij ij = 1 := by
  rw [nnRightInvCLM_toMatrix_entry]
  have hdiag : u.1⁻¹ ij.1.2 ij.1.2 = 1 := by
    have hUUInv : IsUpperUnipotent u.1⁻¹ := Iwasawa.IsUpperUnipotent.inv u.2
    exact hUUInv.2 ij.1.2
  simp [hdiag]

lemma det_nnRightInvCLM_eq_one (u : UU n) :
    LinearMap.det (nnRightInvCLM (n := n) u).toLinearMap = 1 := by
  letI : LinearOrder (nnIndex n) := nnIndexLexLinearOrder n
  rw [← LinearMap.det_toMatrix nnBasis (nnRightInvCLM (n := n) u).toLinearMap]
  rw [Matrix.det_of_lowerTriangular _ (nnRightInvCLM_toMatrix_lowerTriangular (n := n) u)]
  simp [nnRightInvCLM_toMatrix_diag]

lemma abs_det_nnRightInvCLM_eq_one (u : UU n) :
    |LinearMap.det (nnRightInvCLM (n := n) u).toLinearMap| = 1 := by
  rw [det_nnRightInvCLM_eq_one, abs_one]

noncomputable def iwasawaSourceTransportCLM (k : K n) (u : UU n) :
    (Sk n) × ((Fin n → ℝ) × NN n) →L[ℝ]
      (Sk n) × ((Fin n → ℝ) × NN n) :=
  ((skOrthConjCLM (n := n) k).comp
      (ContinuousLinearMap.fst ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
    (((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (NN n)).comp
        (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n))).prod
      ((nnRightInvCLM (n := n) u).comp
        ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (NN n)).comp
          (ContinuousLinearMap.snd ℝ (Sk n) ((Fin n → ℝ) × NN n)))))

@[simp] lemma iwasawaSourceTransportCLM_apply
    (k : K n) (u : UU n) (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    iwasawaSourceTransportCLM (n := n) k u (X, v, Z) =
      (skOrthConjCLM (n := n) k X, (v, nnRightInvCLM (n := n) u Z)) := rfl

lemma iwasawaSourceTransportCLM_toLinearMap_eq_prodMap (k : K n) (u : UU n) :
    (iwasawaSourceTransportCLM (n := n) k u).toLinearMap =
      (skOrthConjCLM (n := n) k).toLinearMap.prodMap
        ((LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)).prodMap
          (nnRightInvCLM (n := n) u).toLinearMap) := by
  apply LinearMap.ext
  intro x
  cases x with
  | mk X p =>
    cases p with
    | mk v Z => rfl

lemma det_iwasawaSourceTransportCLM_eq_sk_mul_nn
    (k : K n) (u : UU n) :
    LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap =
      LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap *
        LinearMap.det (nnRightInvCLM (n := n) u).toLinearMap := by
  rw [iwasawaSourceTransportCLM_toLinearMap_eq_prodMap]
  rw [LinearMap.det_prodMap, LinearMap.det_prodMap, LinearMap.det_id]
  ring

lemma abs_det_iwasawaSourceTransportCLM_eq_sk_mul_nn
    (k : K n) (u : UU n) :
    |LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap| =
      |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| *
        |LinearMap.det (nnRightInvCLM (n := n) u).toLinearMap| := by
  rw [det_iwasawaSourceTransportCLM_eq_sk_mul_nn, abs_mul]

lemma abs_det_iwasawaSourceTransportCLM_eq_sk
    (k : K n) (u : UU n) :
    |LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap| =
      |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| := by
  rw [abs_det_iwasawaSourceTransportCLM_eq_sk_mul_nn,
    abs_det_nnRightInvCLM_eq_one, mul_one]

noncomputable def matrixLeftRightCLM (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ((ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)) A) B

@[simp] lemma matrixLeftRightCLM_apply
    (A B M : Matrix (Fin n) (Fin n) ℝ) :
    matrixLeftRightCLM (n := n) A B M = A * M * B := by
  simp [matrixLeftRightCLM, ContinuousLinearMap.mulLeftRight_apply]

noncomputable def iwasawaTargetTransportCLM (k : K n) (u : UU n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  matrixLeftRightCLM (n := n) k.1 u.1

@[simp] lemma iwasawaTargetTransportCLM_apply
    (k : K n) (u : UU n) (M : Matrix (Fin n) (Fin n) ℝ) :
    iwasawaTargetTransportCLM (n := n) k u M = k.1 * M * u.1 := rfl

lemma matrixLeftRightCLM_toMatrix_stdBasis
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.toMatrix (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (matrixLeftRightCLM (n := n) A B).toLinearMap = A ⊗ₖ B.transpose := by
  ext p q
  rw [LinearMap.toMatrix_apply, matrixStdBasis_repr_apply, Matrix.stdBasis_eq_single]
  change (matrixLeftRightCLM (n := n) A B (Matrix.single q.1 q.2 1)) p.1 p.2 =
    (A ⊗ₖ B.transpose) p q
  rw [matrixLeftRightCLM_apply, Matrix.kroneckerMap_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single q.2]
  · rw [Matrix.mul_single_apply_same]
    simp
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne (c := (1 : ℝ)) q.1 q.2 p.1 b hb A]
    simp
  · intro hb
    simp at hb

lemma det_matrixLeftRightCLM (A B : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (matrixLeftRightCLM (n := n) A B).toLinearMap =
      A.det ^ n * B.det ^ n := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℝ (Fin n) (Fin n))
    (matrixLeftRightCLM (n := n) A B).toLinearMap]
  rw [matrixLeftRightCLM_toMatrix_stdBasis, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin]

lemma abs_det_K_matrix_eq_one (k : K n) : |k.1.det| = 1 := by
  have hsq : k.1.det ^ 2 = 1 := k.2.det_sq
  have habs_sq : |k.1.det| ^ 2 = 1 := by
    rw [← abs_pow, hsq, abs_one]
  exact (sq_eq_one_iff.mp habs_sq).elim (fun h => h) (fun h => by
    linarith [abs_nonneg k.1.det])

lemma abs_det_iwasawaTargetTransportCLM_eq_one (k : K n) (u : UU n) :
    |LinearMap.det (iwasawaTargetTransportCLM (n := n) k u).toLinearMap| = 1 := by
  rw [iwasawaTargetTransportCLM, det_matrixLeftRightCLM, u.2.det]
  simp [abs_det_K_matrix_eq_one (n := n) k, abs_pow]

theorem iwasawaMatrixLeibnizCLM_factored_eq_comp_one_a_one
    (k : K n) (a : A n) (u : UU n) :
    iwasawaMatrixLeibnizCLM k a u =
      (iwasawaTargetTransportCLM (n := n) k u).comp
        ((iwasawaMatrixLeibnizCLM
            (⟨1, IsOrthogonal.one⟩ : K n) a
            (⟨1, IsUpperUnipotent.one⟩ : UU n)).comp
          (iwasawaSourceTransportCLM (n := n) k u)) := by
  apply ContinuousLinearMap.ext
  rintro ⟨X, p⟩
  rcases p with ⟨v, Z⟩
  have hk : k.1 * k.1.transpose = 1 := k.2
  have hu : u.1⁻¹ * u.1 = 1 := Matrix.nonsing_inv_mul u.1 (Ne.isUnit u.2.det_ne_zero)
  have hmat :
      (-(2 : ℝ)) • (X.1 * (k.1 * a.1 * u.1)) +
          k.1 * a.1 * Matrix.diagonal v * u.1 + k.1 * a.1 * Z.1 =
        k.1 * ((-(2 : ℝ)) • ((k.1.transpose * X.1 * k.1) * (1 * a.1 * 1)) +
            1 * a.1 * Matrix.diagonal v * 1 +
            1 * a.1 * (Z.1 * u.1⁻¹)) * u.1 := by
    simp only [one_mul, mul_one]
    rw [Matrix.mul_assoc (k.1.transpose * X.1) k.1 a.1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.add_mul, Matrix.add_mul]
    rw [Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k.1 k.1.transpose]
    rw [hk]
    simp only [one_mul]
    rw [hu]
    simp only [mul_one]
  simpa [iwasawaSourceTransportCLM, iwasawaTargetTransportCLM,
    matrixLeftRightCLM_apply, iwasawaMatrixLeibnizCLM_apply] using hmat

theorem detInIwasawaBases_factored_eq_transport_mul_one_a_one_mul_transport
    (k : K n) (a : A n) (u : UU n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      LinearMap.det (iwasawaTargetTransportCLM (n := n) k u).toLinearMap *
        detInIwasawaBases (iwasawaMatrixLeibnizCLM
          (⟨1, IsOrthogonal.one⟩ : K n) a
          (⟨1, IsUpperUnipotent.one⟩ : UU n)) *
        LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap := by
  rw [iwasawaMatrixLeibnizCLM_factored_eq_comp_one_a_one]
  let S := iwasawaSourceTransportCLM (n := n) k u
  let L := iwasawaMatrixLeibnizCLM
      (⟨1, IsOrthogonal.one⟩ : K n) a (⟨1, IsUpperUnipotent.one⟩ : UU n)
  let T := iwasawaTargetTransportCLM (n := n) k u
  unfold detInIwasawaBases
  change ((LinearMap.toMatrix (iwasawaSourceBasis (n := n))
      (Matrix.stdBasis ℝ (Fin n) (Fin n))
      (T.toLinearMap.comp (L.toLinearMap.comp S.toLinearMap))).det) =
      LinearMap.det T.toLinearMap *
        ((LinearMap.toMatrix (iwasawaSourceBasis (n := n))
          (Matrix.stdBasis ℝ (Fin n) (Fin n)) L.toLinearMap).det) *
        LinearMap.det S.toLinearMap
  rw [LinearMap.toMatrix_comp (iwasawaSourceBasis (n := n))
    (Matrix.stdBasis ℝ (Fin n) (Fin n)) (Matrix.stdBasis ℝ (Fin n) (Fin n))
    T.toLinearMap (L.toLinearMap.comp S.toLinearMap)]
  rw [LinearMap.toMatrix_comp (iwasawaSourceBasis (n := n))
    (iwasawaSourceBasis (n := n)) (Matrix.stdBasis ℝ (Fin n) (Fin n))
    L.toLinearMap S.toLinearMap]
  rw [Matrix.det_mul, Matrix.det_mul]
  rw [LinearMap.det_toMatrix, LinearMap.det_toMatrix]
  ring

theorem absDetInIwasawaBases_factored_eq_transport_mul_one_a_one_mul_transport
    (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      |LinearMap.det (iwasawaTargetTransportCLM (n := n) k u).toLinearMap| *
        absDetInIwasawaBases (iwasawaMatrixLeibnizCLM
          (⟨1, IsOrthogonal.one⟩ : K n) a
          (⟨1, IsUpperUnipotent.one⟩ : UU n)) *
        |LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap| := by
  rw [absDetInIwasawaBases, detInIwasawaBases_factored_eq_transport_mul_one_a_one_mul_transport]
  simp only [absDetInIwasawaBases]
  rw [abs_mul, abs_mul]

theorem detInIwasawaBases_factored_eq_transport_scaled_det_pow_mul_det_adNN
    (k : K n) (a : A n) (u : UU n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      LinearMap.det (iwasawaTargetTransportCLM (n := n) k u).toLinearMap *
        ((2 : ℝ) ^ Fintype.card (nnIndex n) *
          a.1.det ^ n * LinearMap.det (adNN a).toLinearMap) *
        LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap := by
  rw [detInIwasawaBases_factored_eq_transport_mul_one_a_one_mul_transport,
    detInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN]

theorem absDetInIwasawaBases_factored_eq_transport_scaled_det_pow_mul_det_adNN
    (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      |LinearMap.det (iwasawaTargetTransportCLM (n := n) k u).toLinearMap| *
        ((2 : ℝ) ^ Fintype.card (nnIndex n) *
          a.1.det ^ n * LinearMap.det (adNN a).toLinearMap) *
        |LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap| := by
  rw [absDetInIwasawaBases_factored_eq_transport_mul_one_a_one_mul_transport,
    absDetInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN]

theorem absDetInIwasawaBases_factored_eq_source_transport_scaled_det_pow_mul_det_adNN
    (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      ((2 : ℝ) ^ Fintype.card (nnIndex n) *
          a.1.det ^ n * LinearMap.det (adNN a).toLinearMap) *
        |LinearMap.det (iwasawaSourceTransportCLM (n := n) k u).toLinearMap| := by
  rw [absDetInIwasawaBases_factored_eq_transport_scaled_det_pow_mul_det_adNN,
    abs_det_iwasawaTargetTransportCLM_eq_one]
  ring

theorem absDetInIwasawaBases_factored_eq_sk_transport_scaled_det_pow_mul_det_adNN
    (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      ((2 : ℝ) ^ Fintype.card (nnIndex n) *
          a.1.det ^ n * LinearMap.det (adNN a).toLinearMap) *
        |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| := by
  rw [absDetInIwasawaBases_factored_eq_source_transport_scaled_det_pow_mul_det_adNN,
    abs_det_iwasawaSourceTransportCLM_eq_sk]

theorem absDetInIwasawaBases_factored_eq_scaled_det_pow_mul_det_adNN_of_abs_det_skOrthConj
    (k : K n) (a : A n) (u : UU n)
    (hsk : |LinearMap.det (skOrthConjCLM (n := n) k).toLinearMap| = 1) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        a.1.det ^ n * LinearMap.det (adNN a).toLinearMap := by
  rw [absDetInIwasawaBases_factored_eq_sk_transport_scaled_det_pow_mul_det_adNN, hsk, mul_one]

/-! ## T1-6 explicit product formula (Finset.filter form)

Convert from subtype-indexed `∏ ij : nnIndex n` to filter-indexed
`∏ ij ∈ univ.filter (i < j)` via `Finset.prod_subtype`. -/

/-- **T1-6 explicit product formula (filter-indexed).** Matches the
form `∏ ij ∈ Finset.univ.filter (fun ij => ij.1 < ij.2)` used in
downstream Haar / modular-character statements.

Conversion uses `Finset.prod_attach` style indexing between subtype
`nnIndex n` and the filter `Finset.univ.filter (· < ·)`. -/
theorem ad_on_n_det_eq_pair_product (a : A n) :
    LinearMap.det (adNN a).toLinearMap =
      ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ij : Fin n × Fin n => ij.1 < ij.2),
        (a.1 ij.1 ij.1) / (a.1 ij.2 ij.2) := by
  rw [adNN_det_eq_pair_product]
  -- Convert `∏ ij : nnIndex n, f ij.1` to `∏ ij ∈ filter, f ij`.
  -- Use `Finset.prod_subtype` which says
  -- `(∀ x, x ∈ s ↔ p x) → ∏ x ∈ s, f x = ∏ x : {x // p x}, f x`.
  -- Apply symmetrically with `p ij := ij.1 < ij.2` and `s := filter`.
  symm
  apply Finset.prod_subtype
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2))
  intro ij
  simp [Finset.mem_filter]

end JacobianExplicit

end IwasawaCoC

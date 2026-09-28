/-
Iwasawa Lie decomposition, packaged as a single `DirectSum.IsInternal`.

Tier 1, Stage T1-3 (Theorem 2). Repackages the existing pieces in
`IwasawaCoC` — the three pairwise disjointness lemmas, the
codisjointness, and the injectivity of `iwasawaLieMap` — into the
single bundled statement

    `DirectSum.IsInternal ![KK n, AA n, NN n]`

over the index `Fin 3` with `0 ↦ KK n, 1 ↦ AA n, 2 ↦ NN n`. The bridge
is `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` in
`Mathlib/Algebra/DirectSum/Module.lean:513`.

`iSupIndep` is derived from injectivity of `iwasawaLieMap` (the
pairwise disjoint lemmas alone do not suffice for submodule lattices,
which are modular but not distributive). The supremum identity comes
from `iwasawa_codisjoint` combined with `iSup_fin_three`.
-/

import iwasawa_change_of_coords.IwasawaCoC
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.SupIndep

namespace IwasawaCoC

open Matrix Iwasawa
open scoped DirectSum

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The three-component Iwasawa Lie family: `0 ↦ KK n, 1 ↦ AA n, 2 ↦ NN n`. -/
def iwasawaLieFamily (n : ℕ) :
    Fin 3 → Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  ![KK n, AA n, NN n]

@[simp] lemma iwasawaLieFamily_zero : iwasawaLieFamily n 0 = KK n := rfl
@[simp] lemma iwasawaLieFamily_one : iwasawaLieFamily n 1 = AA n := rfl
@[simp] lemma iwasawaLieFamily_two : iwasawaLieFamily n 2 = NN n := rfl

/-- Helper: from `K = a + b` with `K ∈ KK, a ∈ AA, b ∈ NN`, the injectivity
of `iwasawaLieMap` forces `K = 0`. -/
private lemma KK_disjoint_AA_sup_NN : Disjoint (KK n) (AA n ⊔ NN n) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxK : x ∈ KK n := hx.1
  have hxAN : x ∈ AA n ⊔ NN n := hx.2
  rw [Submodule.mem_bot]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxAN
  -- Build `(x, 0, 0)` and `(0, a, b)`; both map to x under iwasawaLieMap.
  have heq : iwasawaLieMap (n := n) (⟨x, hxK⟩, (0 : AA n), (0 : NN n)) =
             iwasawaLieMap (n := n) ((0 : KK n), ⟨a, ha⟩, ⟨b, hb⟩) := by
    show x + (0 : Matrix _ _ ℝ) + (0 : Matrix _ _ ℝ) = (0 : Matrix _ _ ℝ) + a + b
    rw [zero_add, add_zero, add_zero]; exact hab.symm
  -- Injectivity forces the first components equal.
  have h_components := iwasawaLieMap_injective heq
  have hx_eq : (⟨x, hxK⟩ : KK n) = (0 : KK n) := (Prod.ext_iff.mp h_components).1
  have : x = (0 : KK n).1 := congrArg Subtype.val hx_eq
  exact this

/-- Helper for the second iSupIndep clause: `Disjoint (AA n) (NN n ⊔ KK n)`. -/
private lemma AA_disjoint_NN_sup_KK : Disjoint (AA n) (NN n ⊔ KK n) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxA : x ∈ AA n := hx.1
  have hxNK : x ∈ NN n ⊔ KK n := hx.2
  rw [Submodule.mem_bot]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxNK
  -- x ∈ AA, x = a + b with a ∈ NN, b ∈ KK.
  -- Build (0, x, 0) and (b, 0, a); both map to x under iwasawaLieMap.
  have heq : iwasawaLieMap (n := n) ((0 : KK n), ⟨x, hxA⟩, (0 : NN n)) =
             iwasawaLieMap (n := n) (⟨b, hb⟩, (0 : AA n), ⟨a, ha⟩) := by
    show (0 : Matrix _ _ ℝ) + x + (0 : Matrix _ _ ℝ) =
         b + (0 : Matrix _ _ ℝ) + a
    rw [zero_add, add_zero, add_zero, ← hab, add_comm a b]
  have h_components := iwasawaLieMap_injective heq
  have hx_eq : (⟨x, hxA⟩ : AA n) = (0 : AA n) :=
    (Prod.ext_iff.mp (Prod.ext_iff.mp h_components).2).1
  have : x = (0 : AA n).1 := congrArg Subtype.val hx_eq
  exact this

/-- Helper for the third iSupIndep clause: `Disjoint (NN n) (KK n ⊔ AA n)`. -/
private lemma NN_disjoint_KK_sup_AA : Disjoint (NN n) (KK n ⊔ AA n) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxN : x ∈ NN n := hx.1
  have hxKA : x ∈ KK n ⊔ AA n := hx.2
  rw [Submodule.mem_bot]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxKA
  -- x ∈ NN, x = a + b with a ∈ KK, b ∈ AA.
  -- Build (0, 0, x) and (a, b, 0); both map to x.
  have heq : iwasawaLieMap (n := n) ((0 : KK n), (0 : AA n), ⟨x, hxN⟩) =
             iwasawaLieMap (n := n) (⟨a, ha⟩, ⟨b, hb⟩, (0 : NN n)) := by
    show (0 : Matrix _ _ ℝ) + (0 : Matrix _ _ ℝ) + x = a + b + (0 : Matrix _ _ ℝ)
    rw [zero_add, zero_add, add_zero]; exact hab.symm
  have h_components := iwasawaLieMap_injective heq
  have hx_eq : (⟨x, hxN⟩ : NN n) = (0 : NN n) :=
    (Prod.ext_iff.mp (Prod.ext_iff.mp h_components).2).2
  have : x = (0 : NN n).1 := congrArg Subtype.val hx_eq
  exact this

/-- `iSupIndep` for the Iwasawa family, derived from the three
disjointness lemmas above (which in turn use `iwasawaLieMap_injective`). -/
private lemma iwasawaLieFamily_iSupIndep :
    iSupIndep (iwasawaLieFamily n) := by
  rw [iSupIndep_fin_three]
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint (KK n) (AA n ⊔ NN n)
    simp only [iwasawaLieFamily_zero, iwasawaLieFamily_one, iwasawaLieFamily_two]
    exact KK_disjoint_AA_sup_NN
  · -- Disjoint (AA n) (NN n ⊔ KK n)
    simp only [iwasawaLieFamily_zero, iwasawaLieFamily_one, iwasawaLieFamily_two]
    exact AA_disjoint_NN_sup_KK
  · -- Disjoint (NN n) (KK n ⊔ AA n)
    simp only [iwasawaLieFamily_zero, iwasawaLieFamily_one, iwasawaLieFamily_two]
    exact NN_disjoint_KK_sup_AA

/-- The supremum of `KK n, AA n, NN n` is `⊤` (from `iwasawa_codisjoint`). -/
private lemma iwasawaLieFamily_iSup_top :
    ⨆ i, iwasawaLieFamily n i = ⊤ := by
  rw [iSup_fin_three]
  simp only [iwasawaLieFamily_zero, iwasawaLieFamily_one, iwasawaLieFamily_two]
  exact iwasawa_codisjoint n

/-- **Theorem 2.** The Iwasawa Lie decomposition `gl_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫`,
packaged as a single `DirectSum.IsInternal` statement. -/
theorem gl_decomposition_skew_diag_strictUpper :
    DirectSum.IsInternal (iwasawaLieFamily n) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iwasawaLieFamily_iSupIndep, iwasawaLieFamily_iSup_top⟩

/-! ## Milestone 5 (d): `Sym_n = 𝔞 ⊕ 𝔫_sym`

The Iwasawa decomposition refines the symmetric half of the Cartan
decomposition `gl_n = Sym_n ⊕ Sk_n`: a symmetric matrix is its diagonal plus
`X + Xᵀ`, where `X` holds its entries above the diagonal (J-L Ch. I §3, p. 14). -/

/-- `X ↦ X + Xᵀ`, as a linear map on matrices. -/
def symmetrizeLin : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := X + Xᵀ
  map_add' X Y := by simp only [Matrix.transpose_add]; abel
  map_smul' c X := by simp only [Matrix.transpose_smul, smul_add, RingHom.id_apply]

/-- `𝔫_sym = {X + Xᵀ : X ∈ 𝔫}`, the symmetrization of the strictly upper
triangular matrices. -/
noncomputable def NNsym (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := (NN n).map symmetrizeLin

lemma AA_le_Sym : AA n ≤ Sym n := by
  intro M hM
  show M.transpose = M
  ext i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · rw [h]
  · rw [hM j i (Ne.symm h), hM i j h]

lemma NNsym_le_Sym : NNsym n ≤ Sym n := by
  rintro _ ⟨X, -, rfl⟩
  show (X + Xᵀ).transpose = X + Xᵀ
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- **Milestone 5 (d).** `Sym_n = 𝔞 ⊔ 𝔫_sym`. -/
theorem sym_eq_aa_sup_nnSym : Sym n = AA n ⊔ NNsym n := by
  refine le_antisymm ?_ (sup_le AA_le_Sym NNsym_le_Sym)
  intro M hM
  have hMs : M.transpose = M := hM
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then M i j else 0
  let X : Matrix (Fin n) (Fin n) ℝ := fun i j => if i < j then M i j else 0
  have hD : D ∈ AA n := fun i j hij => by simp [D, hij]
  have hX : X ∈ NN n := fun i j hji => by simp [X, not_lt.mpr hji]
  refine Submodule.mem_sup.mpr ⟨D, hD, X + Xᵀ, ⟨X, hX, rfl⟩, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, D, X]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij.ne, hij, not_lt.mpr hij.le]
  · simp
  · have hMij : M j i = M i j := by
      have := congrFun (congrFun hMs i) j
      simpa [Matrix.transpose_apply] using this
    simp [hij.ne', hij, not_lt.mpr hij.le, hMij]

/-- **Milestone 5 (d).** The sum `𝔞 ⊔ 𝔫_sym` is direct. -/
theorem disjoint_AA_NNsym : Disjoint (AA n) (NNsym n) := by
  rw [Submodule.disjoint_def]
  rintro M hA ⟨X, hX, rfl⟩
  ext i j
  by_cases h : i = j
  · subst h
    have hXii : X i i = 0 := hX i i le_rfl
    simp [symmetrizeLin, hXii]
  · simpa using hA i j h

end IwasawaCoC

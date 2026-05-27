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

end IwasawaCoC

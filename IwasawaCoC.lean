/-
Iwasawa decomposition and change of coordinates.

A Lean 4 follow-up to `project.Iwasawa`, formalizing Theorem 1.1 of
Jorgenson and Lang, *Spherical Inversion on SL_n(R)* (Springer, 2001):
the Iwasawa product map `K × A × U → GL_n(ℝ)`, `(k, a, u) ↦ k·a·u`, is
a differential isomorphism.

This file is structured around the core algebraic and topological
milestones (see `README.md`). The smooth diffeomorphism and derivative
layers are completed in the companion files `IwasawaDiffeomorph.lean`,
`IwasawaMFDerivAtOne.lean`, and `IwasawaMFDeriv.lean`.

  1.  `iwasawaEquiv`        — the map is a set-theoretic bijection
  1b. `inv_iwasawa_jl`      — convention swap `kau ↔ uak` (Lang ↔ J-L) via inversion
  1b. `cartanInvolution`    — `θ(g) = (gᵀ)⁻¹`, an order-2 automorphism (J-L p.2)
  2.  `iwasawaHomeomorph`   — topological isomorphism
  3.  `iwasawaDiffeomorph`  — differential isomorphism
  4.  `cartanLieDecomp`     — `gl_n(ℝ) = Sym_n ⊕ Sk_n`
  5.  `iwasawaLieDecomp`    — link to the Iwasawa Lie decomposition

The convention `g = k · a · u` follows Lang's *Linear Algebra* and is
inherited from `project.Iwasawa`. The Jorgenson-Lang convention
`g = u · a · k` is related to Lang's by **inversion**: if `g = k·a·u`
in Lang form, then `g⁻¹ = u⁻¹·a⁻¹·kᵀ` is in J-L form (upper unipotent
× positive diagonal × orthogonal). This identity is `inv_iwasawa_jl`
(Milestone 1b). The Cartan involution `θ(g) = (gᵀ)⁻¹` is a separate
involution which J-L use on p. 2 to characterize `K` as its
fixed-point set.
-/

import project.Iwasawa
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

namespace IwasawaCoC

open Matrix Iwasawa Topology InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace

set_option linter.unusedSectionVars false

variable (n : ℕ)

/-! ## Subgroups as bundled subtypes

We package the three Iwasawa subgroups and the ambient group as plain
subtypes of `Matrix (Fin n) (Fin n) ℝ`. This keeps the API close to
`project.Iwasawa` (which states results in terms of predicates on raw
matrices). Later sections and companion files equip these types with
the topological and smooth structures used by the diffeomorphism and
derivative theorems. -/

/-- The orthogonal group `K = O(n) = { Q | Q · Qᵀ = 1 }`. -/
abbrev K : Type := { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q }

/-- The group `A` of positive diagonal `n × n` real matrices. -/
abbrev A : Type := { D : Matrix (Fin n) (Fin n) ℝ // IsPositiveDiagonal D }

/-- The group `U` of unipotent upper triangular `n × n` real matrices. -/
abbrev UU : Type := { u : Matrix (Fin n) (Fin n) ℝ // IsUpperUnipotent u }

/-- The general linear group `G = GL_n(ℝ)` parameterized as in the parent
project: invertible matrices given by `g.det ≠ 0`. -/
abbrev G : Type := { g : Matrix (Fin n) (Fin n) ℝ // g.det ≠ 0 }

namespace K
  variable {n}
  /-- Underlying matrix of an element of `K`. -/
  abbrev val (Q : K n) : Matrix (Fin n) (Fin n) ℝ := Q.1
  /-- `K n` injects into `GL_n(ℝ)` because orthogonal matrices have nonzero
  determinant (`Iwasawa.IsOrthogonal.det_ne_zero`). -/
  def toG (Q : K n) : G n := ⟨Q.1, Q.2.det_ne_zero⟩
end K

namespace A
  variable {n}
  abbrev val (D : A n) : Matrix (Fin n) (Fin n) ℝ := D.1
  /-- Positive diagonal matrices have positive determinant, in particular
  nonzero, so `A n` injects into `GL_n(ℝ)`. -/
  def toG (D : A n) : G n :=
    ⟨D.1, ne_of_gt D.2.det_pos⟩
end A

namespace UU
  variable {n}
  abbrev val (u : UU n) : Matrix (Fin n) (Fin n) ℝ := u.1
  /-- Unipotent upper triangular matrices have determinant 1, so `UU n`
  injects into `GL_n(ℝ)`. -/
  def toG (u : UU n) : G n := ⟨u.1, u.2.det_ne_zero⟩
end UU

/-! ## Milestone 1: the Iwasawa map is a bijection -/

variable {n}

/-- The Iwasawa product map `K × A × U → GL_n(ℝ)`, `(k, a, u) ↦ k · a · u`. -/
def iwasawaMap : K n × A n × UU n → G n := fun p =>
  let k := p.1; let a := p.2.1; let u := p.2.2
  ⟨k.1 * a.1 * u.1, by
    -- `det (k * a * u) = det k * det a * det u`, all three factors nonzero.
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero
      (mul_ne_zero k.2.det_ne_zero (ne_of_gt a.2.det_pos))
      u.2.det_ne_zero⟩

/-- **Milestone 1.** Theorem 1.1 (set-theoretic part): `iwasawaMap` is a
bijection. The forward direction is the parent project's
`Iwasawa.exists_iwasawa`; injectivity is `Iwasawa.iwasawa_unique`. -/
noncomputable def iwasawaEquiv : K n × A n × UU n ≃ G n where
  toFun := iwasawaMap
  invFun g :=
    let F := Iwasawa.iwasawa g.2
    (⟨F.k, F.k_orthogonal⟩, ⟨F.a, F.a_positiveDiagonal⟩, ⟨F.u, F.u_upperUnipotent⟩)
  left_inv := by
    rintro ⟨k, a, u⟩
    -- An explicit alternative factorization built from `(k, a, u)`.
    let F' : Iwasawa.IwasawaFactorization (k.1 * a.1 * u.1) :=
      { k := k.1, a := a.1, u := u.1
        k_orthogonal := k.2
        a_positiveDiagonal := a.2
        u_upperUnipotent := u.2
        factorization := rfl }
    -- By uniqueness, `Iwasawa.iwasawa _` agrees with `F'` on each component.
    obtain ⟨hk, ha, hu⟩ :=
      Iwasawa.iwasawa_unique (Iwasawa.iwasawa (iwasawaMap (k, a, u)).2) F'
    exact Prod.ext (Subtype.ext hk) (Prod.ext (Subtype.ext ha) (Subtype.ext hu))
  right_inv := by
    intro g
    apply Subtype.ext
    -- After unfolding `iwasawaMap` and `invFun`, the goal reduces to
    -- `(Iwasawa.iwasawa g.2).k * .a * .u = g.1`, which is `factorization.symm`.
    exact (Iwasawa.iwasawa g.2).factorization.symm

/-! ## Milestone 1b: the Cartan involution and convention swap

Jorgenson-Lang state Theorem 1.1 as `G = U · A · K` (U on the left); we
have the parent's convention `G = K · A · U`. The change of coordinates
between the two is the **Cartan involution**

    θ : GL_n(ℝ) → GL_n(ℝ),    θ(g) = (gᵀ)⁻¹.

`θ` is an order-2 group automorphism; it carries `K` to `K`, `A` to
`A⁻¹` (still `A`), and `U` (upper unipotent) to lower unipotent,
which is `U` again after relabelling rows/columns (or after one
additional transposition). We formalize the involutivity here and use
it to convert between the two factorization orders. -/

/-- The Cartan involution `θ(g) = (gᵀ)⁻¹` on `GL_n(ℝ)`. -/
noncomputable def cartanInvolution : G n → G n := fun g =>
  ⟨(g.1.transpose)⁻¹, by
    -- If `M.det ≠ 0` then `M⁻¹.det ≠ 0`, since `M * M⁻¹ = 1` forces
    -- `det M * det M⁻¹ = 1`, so neither factor can be zero.
    have hT : g.1.transpose.det ≠ 0 := by
      rw [Matrix.det_transpose]; exact g.2
    have hUnit : IsUnit g.1.transpose.det := isUnit_iff_ne_zero.mpr hT
    intro h
    have hMul : g.1.transpose * (g.1.transpose)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hUnit
    have hDet : g.1.transpose.det * ((g.1.transpose)⁻¹).det = 1 := by
      rw [← Matrix.det_mul, hMul, Matrix.det_one]
    rw [h, mul_zero] at hDet
    exact zero_ne_one hDet⟩

theorem cartanInvolution_involutive : Function.Involutive (cartanInvolution : G n → G n) := by
  intro g
  apply Subtype.ext
  -- Goal: `(((g.transpose)⁻¹).transpose)⁻¹ = g`. Apply
  --   `transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹`        (with A := g.1.transpose)
  --   `transpose_transpose   : Mᵀᵀ = M`
  --   `nonsing_inv_nonsing_inv : M⁻¹⁻¹ = M`         (using IsUnit g.1.det)
  -- in sequence to reduce `(((Mᵀ)⁻¹)ᵀ)⁻¹` to `M`.
  have hUnit : IsUnit g.1.det := isUnit_iff_ne_zero.mpr g.2
  show ((g.1.transpose)⁻¹.transpose)⁻¹ = g.1
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.nonsing_inv_nonsing_inv _ hUnit]

/-- **Milestone 1b: convention swap.** If `g = k · a · u` is Lang's Iwasawa
factorization, then `g⁻¹ = u⁻¹ · a⁻¹ · kᵀ` is the Jorgenson-Lang
factorization of `g⁻¹`: the right-hand side is upper-unipotent times
positive-diagonal times orthogonal, matching J-L's `g = u · a · k` form. -/
theorem inv_iwasawa_jl (k : K n) (a : A n) (u : UU n) :
    (k.1 * a.1 * u.1)⁻¹ = u.1⁻¹ * a.1⁻¹ * k.1.transpose := by
  -- `(k * a * u)⁻¹ = u⁻¹ * (k * a)⁻¹ = u⁻¹ * (a⁻¹ * k⁻¹)`, and `k⁻¹ = kᵀ`.
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mul_assoc,
      Iwasawa.IsOrthogonal.matInv_eq_transpose k.2]

/-- The factors `u⁻¹`, `a⁻¹`, `kᵀ` on the right-hand side of
`inv_iwasawa_jl` indeed live in the appropriate subgroups. -/
theorem inv_iwasawa_jl_components
    (k : K n) (a : A n) (u : UU n) :
    IsUpperUnipotent u.1⁻¹ ∧ IsPositiveDiagonal a.1⁻¹ ∧ IsOrthogonal k.1.transpose :=
  ⟨u.2.inv, a.2.matInv, k.2.transpose⟩

/-! ## Milestone 2: topological structure

The four subgroup types are bundled subtypes of
`Matrix (Fin n) (Fin n) ℝ`, which is itself a finite product of copies
of ℝ (hence a topological ring via `Matrix.topologicalRing`). The
subspace topologies on `K n`, `A n`, `UU n`, `G n` are inferred
automatically from the `abbrev` definitions (no instance declarations
needed).

The forward direction `iwasawaMap` is continuous because matrix
multiplication is continuous (`Continuous.matrix_mul`) and the
subtype embeddings are continuous. -/

/-- **Milestone 2 forward.** The Iwasawa product map is continuous. -/
theorem continuous_iwasawaMap : Continuous (iwasawaMap : K n × A n × UU n → G n) := by
  apply Continuous.subtype_mk
  refine Continuous.matrix_mul (Continuous.matrix_mul ?_ ?_) ?_
  · exact (continuous_subtype_val.comp continuous_fst)
  · exact (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  · exact (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

/-! ### Continuity of the inverse map via Gram–Schmidt continuity

Wikipedia ("Gram–Schmidt process") gives a determinant-based closed
form for each output vector, showing rationality. We prove continuity
directly by induction on the index using Mathlib's `gramSchmidt_def`
recursion and `Submodule.starProjection_singleton` (which expresses
the 1D projection as `(⟨v, w⟩ / ‖v‖²) • v`, continuous when `v ≠ 0`).

The denominator `‖v‖² = ‖gramSchmidt ℝ (gCol g.1) j‖²` is nonzero on
`G n` because `gCol g.1` is linearly independent there
(`Iwasawa.gCol_linearIndependent`), so `gramSchmidt` outputs are
nonzero (`gramSchmidt_ne_zero`). -/

private lemma continuous_gCol_at (i : Fin n) :
    Continuous (fun g : Matrix (Fin n) (Fin n) ℝ => Iwasawa.gCol g i) := by
  unfold Iwasawa.gCol
  fun_prop

/-- For each `i`, `g ↦ gramSchmidt ℝ (gCol g.1) i` is continuous on `G n`. -/
private lemma continuous_gramSchmidt_at (i : Fin n) :
    Continuous (fun g : G n => gramSchmidt ℝ (Iwasawa.gCol g.1) i) := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    -- Rewrite using `gramSchmidt_def`.
    have heq : (fun g : G n => gramSchmidt ℝ (Iwasawa.gCol g.1) i) =
        fun g : G n => Iwasawa.gCol g.1 i -
          ∑ j ∈ Finset.Iio i,
            (ℝ ∙ gramSchmidt ℝ (Iwasawa.gCol g.1) j).starProjection (Iwasawa.gCol g.1 i) := by
      funext g
      exact gramSchmidt_def ℝ _ i
    rw [heq]
    have hcGCol : Continuous (fun g : G n => Iwasawa.gCol g.1 i) :=
      (continuous_gCol_at i).comp continuous_subtype_val
    refine Continuous.sub hcGCol ?_
    apply continuous_finset_sum
    intro j hj
    have hji : j < i := Finset.mem_Iio.mp hj
    have ihj : Continuous (fun g : G n => gramSchmidt ℝ (Iwasawa.gCol g.1) j) := ih j hji
    -- Apply `starProjection_singleton` pointwise: `(ℝ ∙ v).starProjection w = (⟨v,w⟩/‖v‖²) • v`.
    have hsp : (fun g : G n =>
        (ℝ ∙ gramSchmidt ℝ (Iwasawa.gCol g.1) j).starProjection (Iwasawa.gCol g.1 i)) =
        fun g : G n =>
          (((⟪gramSchmidt ℝ (Iwasawa.gCol g.1) j, Iwasawa.gCol g.1 i⟫_ℝ) /
            ((‖gramSchmidt ℝ (Iwasawa.gCol g.1) j‖ ^ 2 : ℝ))) •
            gramSchmidt ℝ (Iwasawa.gCol g.1) j) := by
      funext g
      simpa using Submodule.starProjection_singleton ℝ (Iwasawa.gCol g.1 i)
    rw [hsp]
    -- Continuity of the rational expression times a continuous vector.
    refine Continuous.smul ?_ ihj
    have hInner : Continuous (fun g : G n =>
        ⟪gramSchmidt ℝ (Iwasawa.gCol g.1) j, Iwasawa.gCol g.1 i⟫_ℝ) :=
      ihj.inner hcGCol
    have hNormSq : Continuous (fun g : G n =>
        ((‖gramSchmidt ℝ (Iwasawa.gCol g.1) j‖ : ℝ) ^ 2)) :=
      (ihj.norm).pow 2
    have hNZ : ∀ g : G n, ((‖gramSchmidt ℝ (Iwasawa.gCol g.1) j‖ : ℝ) ^ 2) ≠ 0 := fun g => by
      have hne : gramSchmidt ℝ (Iwasawa.gCol g.1) j ≠ 0 :=
        gramSchmidt_ne_zero j (Iwasawa.gCol_linearIndependent g.2)
      have : (0 : ℝ) < ‖gramSchmidt ℝ (Iwasawa.gCol g.1) j‖ := norm_pos_iff.mpr hne
      positivity
    exact hInner.div hNormSq hNZ

/-- `g ↦ gramSchmidtNormed ℝ (gCol g.1) i` is continuous on `G n`. -/
private lemma continuous_gramSchmidtNormed_at (i : Fin n) :
    Continuous (fun g : G n => gramSchmidtNormed ℝ (Iwasawa.gCol g.1) i) := by
  -- gramSchmidtNormed f n = (‖gramSchmidt f n‖ : 𝕜)⁻¹ • gramSchmidt f n
  unfold gramSchmidtNormed
  refine Continuous.smul ?_ (continuous_gramSchmidt_at i)
  refine Continuous.inv₀ (continuous_gramSchmidt_at i).norm (fun g => ?_)
  -- ‖gramSchmidt ℝ (gCol g.1) i‖ ≠ 0
  have hne : gramSchmidt ℝ (Iwasawa.gCol g.1) i ≠ 0 :=
    gramSchmidt_ne_zero i (Iwasawa.gCol_linearIndependent g.2)
  exact ne_of_gt (norm_pos_iff.mpr hne)

/-- `qMat` is continuous on `G n`. -/
private lemma continuous_qMat_subtype :
    Continuous (fun g : G n => Iwasawa.qMat g.1) := by
  -- qMat g = fun j i => gsCol g i j. Show continuous entry-by-entry.
  apply continuous_matrix
  intro j i
  show Continuous (fun g : G n => Iwasawa.qMat g.1 j i)
  -- qMat g.1 j i = gsCol g.1 i j; the latter is the j-th coordinate of
  -- the EuclideanSpace vector gsCol g.1 i. Chain through PiLp.continuous_ofLp.
  have hgs : Continuous (fun g : G n => Iwasawa.gsCol g.1 i) := by
    unfold Iwasawa.gsCol
    exact continuous_gramSchmidtNormed_at i
  -- Goal: Continuous (fun g => (gsCol g.1 i) j) where (gsCol g.1 i) : EuclideanSpace ℝ (Fin n).
  -- PiLp.continuous_apply j gives continuity of `fun f : PiLp 2 _ => f j`; compose with hgs.
  exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) j).comp hgs

/-- `dMat` is continuous on `G n`. -/
private lemma continuous_dMat_subtype :
    Continuous (fun g : G n => Iwasawa.dMat g.1) := by
  -- dMat g i j = if i = j then rMat g i i else 0
  -- where rMat g i j = ⟪gsCol g i, gCol g j⟫_ℝ.
  apply continuous_matrix
  intro i j
  show Continuous (fun g : G n => Iwasawa.dMat g.1 i j)
  unfold Iwasawa.dMat
  by_cases hij : i = j
  · simp only [hij, if_true]
    -- Continuous (fun g => rMat g.1 j j) = ⟪gsCol g.1 j, gCol g.1 j⟫
    show Continuous (fun g : G n => Iwasawa.rMat g.1 j j)
    unfold Iwasawa.rMat Iwasawa.gsCol
    exact (continuous_gramSchmidtNormed_at j).inner
      ((continuous_gCol_at j).comp continuous_subtype_val)
  · simp only [hij, if_false]
    exact continuous_const

/-- `rMat` is continuous on `G n` (helper for `uMat`). -/
private lemma continuous_rMat_subtype :
    Continuous (fun g : G n => Iwasawa.rMat g.1) := by
  apply continuous_matrix
  intro p q
  show Continuous (fun g : G n => Iwasawa.rMat g.1 p q)
  unfold Iwasawa.rMat Iwasawa.gsCol
  exact (continuous_gramSchmidtNormed_at p).inner
    ((continuous_gCol_at q).comp continuous_subtype_val)

/-- `diagInv (dMat g)` is continuous on `G n`. -/
private lemma continuous_diagInv_dMat_subtype :
    Continuous (fun g : G n => Iwasawa.diagInv (Iwasawa.dMat g.1)) := by
  apply continuous_matrix
  intro p q
  show Continuous (fun g : G n => Iwasawa.diagInv (Iwasawa.dMat g.1) p q)
  unfold Iwasawa.diagInv
  by_cases hpq : p = q
  · simp only [hpq, if_true]
    refine Continuous.inv₀ ?_ (fun g => ?_)
    · exact (continuous_dMat_subtype).matrix_elem q q
    · exact ne_of_gt ((Iwasawa.dMat_isPositiveDiagonal g.2).2 q)
  · simp only [hpq, if_false]
    exact continuous_const

/-- `uMat` is continuous on `G n`. -/
private lemma continuous_uMat_subtype :
    Continuous (fun g : G n => Iwasawa.uMat g.1) := by
  -- uMat g = diagInv (dMat g) * rMat g.
  unfold Iwasawa.uMat
  exact Continuous.matrix_mul continuous_diagInv_dMat_subtype continuous_rMat_subtype

/-- **Milestone 2 inverse direction.** The inverse of the Iwasawa map is
continuous on `G n`. -/
theorem continuous_iwasawaSymm :
    Continuous (iwasawaEquiv (n := n)).symm := by
  -- iwasawaEquiv.symm g = (⟨qMat g.1, _⟩, ⟨dMat g.1, _⟩, ⟨uMat g.1, _⟩)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact continuous_qMat_subtype.subtype_mk _
  · exact continuous_dMat_subtype.subtype_mk _
  · exact continuous_uMat_subtype.subtype_mk _

/-- **Milestone 2.** The Iwasawa map is a homeomorphism. -/
noncomputable def iwasawaHomeomorph : K n × A n × UU n ≃ₜ G n where
  toEquiv := iwasawaEquiv
  continuous_toFun := continuous_iwasawaMap
  continuous_invFun := continuous_iwasawaSymm

/-! ## Milestone 3: smooth structure

For the differential isomorphism statement we need smooth manifold
structures on `K n`, `A n`, `UU n`, `G n`. The status of each in
Mathlib v4.30:

  * `G n = {g : Matrix … // g.det ≠ 0}` is an *open* subset of
    `Matrix (Fin n) (Fin n) ℝ` (preimage of `≠ 0` under the continuous
    determinant), hence inherits a smooth manifold structure as an
    open submanifold of the model space. Mathlib's
    `IsOpenEmbedding.singletonChartedSpace` and
    `IsOpenEmbedding.isManifold_singleton` provide this in one line
    (cf. `Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra`).
  * `UU n = {u | IsUpperUnipotent u}` is an affine subspace of
    Matrix of dimension `n(n-1)/2`. Smooth structure is straightforward
    via the natural chart (read off the strictly-upper-triangular
    entries).
  * `A n = {D | IsPositiveDiagonal D}` is an open subset of the
    *diagonal* subspace, of dimension `n`. Smooth structure via the
    log map (log : (ℝ⁺)ⁿ → ℝⁿ).
  * `K n = O(n)` is a compact smooth submanifold of dimension
    `n(n-1)/2`, cut out by the polynomial equations `Q · Qᵀ = 1`.
    Mathlib does not currently package `O(n)` as a smooth submanifold
    of `Matrix`, although the underlying constant-rank /
    inverse-function-theorem machinery is present.

The forward and inverse smoothness statements, and the bundled
`Diffeomorph`, are now proved in `IwasawaDiffeomorph.lean`. The
historical Gram-Schmidt smoothness route is no longer the active
blocker for this project. -/

-- Smooth structure on G n via the open-embedding construction.
-- (G n is an open subset of `Matrix (Fin n) (Fin n) ℝ` since `det` is continuous.)

/-- `G n` is open in `Matrix (Fin n) (Fin n) ℝ`. -/
theorem isOpen_G : IsOpen { g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0 } :=
  (isClosed_singleton.preimage (continuous_id.matrix_det)).isOpen_compl

/-- The inclusion `G n ↪ Matrix (Fin n) (Fin n) ℝ` is an open embedding. -/
theorem G_isOpenEmbedding :
    IsOpenEmbedding (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) :=
  isOpen_G.isOpenEmbedding_subtypeVal

/-- `G n` is nonempty (the identity matrix has determinant `1 ≠ 0`). -/
instance : Nonempty (G n) := ⟨⟨1, by simp⟩⟩

section SmoothG

-- We choose Mathlib's elementwise sup-norm on matrices for the manifold
-- structure on `G n`. This is `Matrix.normedAddCommGroup` from
-- `Mathlib.Analysis.Matrix.Normed`, registered as `@[instance_reducible]`
-- non-instances. We expose them only inside this section because Mathlib
-- intentionally avoids globally fixing one matrix norm.
attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

/-- Smooth structure on `G n` (as an open submanifold of Matrix). -/
noncomputable instance instChartedSpaceG :
    ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (G n) :=
  G_isOpenEmbedding.singletonChartedSpace

instance instIsManifoldG :
    IsManifold (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤ (G n) :=
  G_isOpenEmbedding.isManifold_singleton

end SmoothG

-- TODO(milestone 3, K smooth): set up `ChartedSpace`/`IsManifold` on `K n`
-- as an embedded submanifold cut out by `Q · Qᵀ = 1`. This requires
-- formalizing `O(n)` as a smooth submanifold of `Matrix` via Cayley-transform
-- charts (or stereographic-style local charts, following the pattern of
-- `Mathlib.Geometry.Manifold.Instances.Sphere`). Substantial Mathlib-level
-- work; deferred.

-- TODO(milestone 3, UU smooth): smooth structure on `UU n` via
-- the homeomorphism `UU n ≃ₜ NN n` given by `U ↦ U - 1`. The
-- homeomorphism construction and `IsManifold` instance live below
-- in the Milestone-5 area (after `NN n` is introduced).

-- TODO(milestone 3, A smooth): smooth structure on `A n` modeled on
-- `AA n` via the open inclusion (positivity is open on each diagonal
-- entry). Deferred.

/-! ## Milestone 4: Cartan Lie decomposition `gl_n(ℝ) = Sym_n ⊕ Sk_n`

This is the linear-algebraic content of Jorgenson-Lang §I.3. It is
independent of Milestones 2–3 and can be proved any time. -/

/-- Symmetric `n × n` real matrices. -/
def Sym (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := { M | M.transpose = M }
  zero_mem' := Matrix.transpose_zero
  add_mem' := by
    intro M N hM hN
    show (M + N).transpose = M + N
    rw [Matrix.transpose_add, hM, hN]
  smul_mem' := by
    intro c M hM
    show (c • M).transpose = c • M
    rw [Matrix.transpose_smul, hM]

/-- Skew-symmetric `n × n` real matrices. -/
def Sk (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := { M | M.transpose = -M }
  zero_mem' := by show (0 : Matrix (Fin n) (Fin n) ℝ).transpose = -0; simp
  add_mem' := by
    intro M N hM hN
    show (M + N).transpose = -(M + N)
    rw [Matrix.transpose_add, hM, hN, neg_add]
  smul_mem' := by
    intro c M hM
    show (c • M).transpose = -(c • M)
    rw [Matrix.transpose_smul, hM, smul_neg]

/-- **Milestone 4.** `gl_n(ℝ) = Sym_n ⊕ Sk_n` as a direct sum of subspaces.

Explicitly, every `M ∈ Mat_n(ℝ)` decomposes uniquely as
`M = ½(M + Mᵀ) + ½(M − Mᵀ)`. -/
theorem cartanLieDecomp (n : ℕ) : IsCompl (Sym n) (Sk n) := by
  refine ⟨?_, ?_⟩
  · -- Disjoint: if `M ∈ Sym ∩ Sk` then `Mᵀ = M = -M`, so `2M = 0`, so `M = 0`.
    rw [disjoint_iff_inf_le]
    intro M hM
    obtain ⟨hSym, hSk⟩ := hM
    -- `hSym : M.transpose = M`, `hSk : M.transpose = -M`
    change M.transpose = M at hSym
    change M.transpose = -M at hSk
    have hNeg : M = -M := hSym.symm.trans hSk
    have hSum : M + M = 0 := by
      have : M + M = M + (-M) := by rw [← hNeg]
      rw [this]; exact add_neg_cancel M
    have h2 : (2 : ℝ) • M = 0 := by rw [two_smul]; exact hSum
    have hM_zero : M = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
    rw [Submodule.mem_bot]
    exact hM_zero
  · -- Codisjoint: every `M` lies in `Sym ⊔ Sk` via `M = ½(M+Mᵀ) + ½(M−Mᵀ)`.
    rw [codisjoint_iff_le_sup]
    intro M _
    rw [Submodule.mem_sup]
    refine ⟨(1/2 : ℝ) • (M + M.transpose), ?_,
            (1/2 : ℝ) • (M - M.transpose), ?_, ?_⟩
    · -- `½(M + Mᵀ) ∈ Sym`
      change ((1/2 : ℝ) • (M + M.transpose)).transpose = (1/2 : ℝ) • (M + M.transpose)
      rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
    · -- `½(M − Mᵀ) ∈ Sk`
      change ((1/2 : ℝ) • (M - M.transpose)).transpose = -((1/2 : ℝ) • (M - M.transpose))
      rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose,
          ← smul_neg, neg_sub]
    · -- `½(M + Mᵀ) + ½(M − Mᵀ) = M`
      rw [smul_add, smul_sub]
      -- Group the two `½ • Mᵀ` terms which cancel, leaving `½M + ½M = M`.
      have hCancel :
          ((1 : ℝ)/2) • M + ((1 : ℝ)/2) • M.transpose
            + (((1 : ℝ)/2) • M - ((1 : ℝ)/2) • M.transpose)
          = ((1 : ℝ)/2) • M + ((1 : ℝ)/2) • M := by abel
      rw [hCancel, ← add_smul]
      norm_num

/-! ## Milestone 5: linking the global and infinitesimal pictures

The Lie subalgebras of `gl_n(ℝ)` corresponding to the three Iwasawa
factors are

  * `𝔫 = nₙ` — strictly upper triangular matrices (`Lie(U)`),
  * `𝔞 = aₙ` — real diagonal matrices (`Lie(A)`),
  * `𝔨 = Sk_n` — skew-symmetric matrices (`Lie(K) = Lie(O(n))`).

The Iwasawa Lie decomposition

    gl_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫                                  (*)

realizes the differential of the Iwasawa map `Φ` at the identity
`(1, 1, 1)`: the tangent space at `1` of each factor is the
corresponding subalgebra, and the differential
`(dΦ)_{(1,1,1)} : 𝔨 × 𝔞 × 𝔫 → gl_n(ℝ)` is the inclusion sum
`(X, Y, Z) ↦ X + Y + Z`, which is an isomorphism by (*).

Compared to the Cartan Lie decomposition `gl_n = Sym ⊕ Sk` of
Milestone 4, the Iwasawa decomposition (*) refines `Sym` into
`𝔞 ⊕ 𝔫_sym` where `𝔫_sym = {X + Xᵀ : X ∈ 𝔫}` is the symmetrization
of the strictly upper triangular part (compare J-L Ch. I §3, p. 14). -/

/-- The Lie subalgebra `𝔫` of strictly upper triangular matrices. -/
def NN (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := { M | ∀ i j, j ≤ i → M i j = 0 }
  zero_mem' := by intros _ _ _; rfl
  add_mem' := by
    intro M N hM hN i j hij
    simp [hM i j hij, hN i j hij]
  smul_mem' := by
    intro c M hM i j hij
    simp [hM i j hij]

/-- The Lie subalgebra `𝔞` of real diagonal matrices. -/
def AA (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := { M | ∀ i j, i ≠ j → M i j = 0 }
  zero_mem' := by intros _ _ _; rfl
  add_mem' := by
    intro M N hM hN i j hij
    simp [hM i j hij, hN i j hij]
  smul_mem' := by
    intro c M hM i j hij
    simp [hM i j hij]

/-- The Lie subalgebra `𝔨 = Sk_n` (already defined as `Sk` in Milestone 4). -/
abbrev KK (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := Sk n

/-- **Milestone 5 (a).** `𝔞 ⊓ 𝔫 = ⊥`: the only matrix that is both diagonal and
strictly upper triangular is the zero matrix. -/
theorem disjoint_AA_NN (n : ℕ) : Disjoint (AA n) (NN n) := by
  rw [disjoint_iff_inf_le]
  intro M ⟨hAA, hNN⟩
  rw [Submodule.mem_bot]
  ext i j
  -- `hAA : ∀ i j, i ≠ j → M i j = 0`, `hNN : ∀ i j, j ≤ i → M i j = 0`.
  rcases eq_or_ne i j with rfl | hij
  · -- diagonal case: NN says `M i i = 0` since `i ≤ i`.
    exact (hNN i i le_rfl).trans rfl.symm
  · -- off-diagonal case: AA says `M i j = 0`.
    exact (hAA i j hij).trans rfl.symm

/-- **Milestone 5 (b).** `𝔨 ⊓ 𝔞 = ⊥`: a skew-symmetric diagonal matrix is zero
(skew-symmetry forces `M_{ii} = -M_{ii}`, off-diagonal forces it to vanish). -/
theorem disjoint_KK_AA (n : ℕ) : Disjoint (KK n) (AA n) := by
  rw [disjoint_iff_inf_le]
  intro M ⟨hKK, hAA⟩
  rw [Submodule.mem_bot]
  ext i j
  -- `hKK : M.transpose = -M`, so `M j i = -M i j` for all i, j.
  -- `hAA : ∀ i j, i ≠ j → M i j = 0`.
  rcases eq_or_ne i j with rfl | hij
  · -- `M i i = -M i i` forces `2 • M i i = 0`, so `M i i = 0`.
    have : M i i = -M i i := by
      have := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i) hKK
      simpa using this
    have h2 : M i i + M i i = 0 := by linarith
    have h3 : (2 : ℝ) * M i i = 0 := by linarith
    have h4 : M i i = 0 := by linarith
    exact h4.trans rfl.symm
  · exact (hAA i j hij).trans rfl.symm

/-- **Milestone 5 (c).** `𝔨 ⊓ 𝔫 = ⊥`: a strictly upper triangular skew-symmetric
matrix is zero (the entries below the diagonal are zero by transpose-skew of
the strictly-upper zeros, and the strictly-upper entries themselves vanish by
the same skew-transpose argument applied across the diagonal). -/
theorem disjoint_KK_NN (n : ℕ) : Disjoint (KK n) (NN n) := by
  rw [disjoint_iff_inf_le]
  intro M ⟨hKK, hNN⟩
  rw [Submodule.mem_bot]
  ext i j
  -- For i > j: `M i j = 0` by NN (since `j ≤ i`).
  -- For i = j: `M i i = 0` (already by NN with `i ≤ i`).
  -- For i < j: `M i j = -M j i` by skew, but `M j i = 0` since `i ≤ j` means `j > i`,
  --   so `i ≤ j`, hence `M j i = 0` by NN. Therefore `M i j = -0 = 0`.
  by_cases hij : j ≤ i
  · exact (hNN i j hij).trans rfl.symm
  · push Not at hij  -- `i < j`
    -- skew gives `M i j = -M j i`, and NN gives `M j i = 0` (since `i ≤ j`).
    have hMji : M j i = 0 := hNN j i hij.le
    have hSkew : M.transpose i j = -M i j := by
      have := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hKK
      simpa using this
    -- `M.transpose i j = M j i = 0`, combined with `= -M i j` gives `M i j = 0`.
    have : M j i = -M i j := by simpa using hSkew
    have hMij : M i j = -M j i := by linarith
    rw [hMij, hMji]; simp

/-- **Milestone 5 (d).** Sym = 𝔞 ⊕ 𝔫_sym, where `𝔫_sym = {X + Xᵀ : X ∈ 𝔫}`.
Statement and proof deferred — requires defining the symmetrization
submodule `𝔫_sym`. (See J-L Ch. I §3, p. 14.) -/
theorem sym_eq_aa_add_n_sym :
    -- Decomposition: any symmetric M = diag(M) + (strictUpper(M) + strictUpper(M)ᵀ).
    -- Statement deferred (see README §"What's deferred").
    True := trivial

/-- **Milestone 5 (e).** Codisjointness: `𝔨 ⊔ 𝔞 ⊔ 𝔫 = ⊤`. Combined with the
three `disjoint_*` lemmas above this gives the Iwasawa Lie decomposition
`gl_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫` as an internal direct sum.

The decomposition `M = K + A + N` of an arbitrary `M ∈ Mat_n(ℝ)`:
* `A_{ij} = M_{ii}` if `i = j`, else `0`              (diagonal of `M`),
* `K_{ij} = M_{ij}` if `j < i`, `K_{ij} = -M_{ji}` if `i < j`, else `0`
  (skew-symmetrization of the strictly-lower part of `M`),
* `N_{ij} = M_{ij} + M_{ji}` if `i < j`, else `0`     (strict upper).

The proof verifies the three submodule memberships and the equation
entry-by-entry, splitting on the trichotomy `j < i / i = j / i < j`. -/
theorem iwasawa_codisjoint (n : ℕ) : KK n ⊔ AA n ⊔ NN n = ⊤ := by
  rw [eq_top_iff]
  intro M _
  -- Explicit components.
  set A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun i j => if i = j then M i i else 0) with hA
  set K : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun i j => if j < i then M i j
                          else if i < j then -M j i else 0) with hK
  set N : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun i j => if i < j then M i j + M j i else 0) with hN
  -- M = (K + A) + N: first build K + A ∈ KK ⊔ AA, then add N ∈ NN.
  rw [Submodule.mem_sup]
  refine ⟨K + A, ?_, N, ?_, ?_⟩
  · rw [Submodule.mem_sup]
    refine ⟨K, ?_, A, ?_, rfl⟩
    · -- K ∈ KK = Sk: K.transpose = -K, i.e., K j i = -K i j for all i j.
      change K.transpose = -K
      ext i j
      rw [Matrix.transpose_apply, Matrix.neg_apply, hK]
      simp only [Matrix.of_apply]
      rcases lt_trichotomy j i with hji | hij_eq | hij
      · -- j < i: K(j,i) goes to else-else (i < j is false, j < i is false from j-perspective at swap)
        --   K i j (RHS arg before neg) = (j < i)-branch = M i j; -(K i j) = -M i j
        --   K j i (LHS) = need: at (j,i), j < i? we're querying K(j,i): does i < j? no (since j < i). does j < i? we're querying with first arg j, second arg i, so "j < i" in K's body means "first < second" = j < i. Hmm let me re-read K's definition:
        -- K = fun i j => if j < i then M i j else if i < j then -M j i else 0
        -- So K(p,q) = if q < p then M p q else if p < q then -M q p else 0
        -- K(j,i) = if i < j then M j i else if j < i then -M i j else 0 = -M i j (using j < i)
        -- -K(i,j) = -(if j < i then M i j else ...) = -M i j (using j < i)
        rw [if_neg (lt_asymm hji), if_pos hji, if_pos hji]
      · -- i = j: K(i,i) = 0 = -K(i,i)
        subst hij_eq
        simp
      · -- i < j: K(j,i) = M j i (using j > i, so i < j); -K(i,j) = -(-M j i) = M j i
        rw [if_pos hij, if_neg (lt_asymm hij), if_pos hij, neg_neg]
    · -- A ∈ AA: zero off the diagonal.
      intro i j hij
      simp [hA, hij]
  · -- N ∈ NN: zero on `j ≤ i`.
    intro i j hji
    simp [hN, not_lt.mpr hji]
  · -- (K + A) + N = M, by entry-by-entry case analysis.
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply, hK, hA, hN]
    simp only [Matrix.of_apply]
    rcases lt_trichotomy j i with hji | hij_eq | hij
    · -- j < i (below diagonal): A_ij = 0 (i ≠ j), K_ij = M_ij, N_ij = 0 (¬ i < j).
      rw [if_pos hji, if_neg (ne_of_gt hji), if_neg (lt_asymm hji)]
      ring
    · -- i = j (diagonal): K_ii = 0, A_ii = M_ii, N_ii = 0.
      subst hij_eq
      simp
    · -- i < j (above diagonal): K_ij = -M_ji (¬ j < i, but i < j), A_ij = 0, N_ij = M_ij + M_ji.
      rw [if_neg (lt_asymm hij), if_pos hij, if_neg (ne_of_lt hij), if_pos hij]
      ring

/-- **Milestone 5 (f).** The Iwasawa Lie decomposition: pairwise disjoint
+ codisjoint = direct-sum decomposition `gl_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫`.

This is the bundled form: an `iSupIndep` family combined with
`iSup = ⊤`. Stated here as the conjunction of the four conditions
proved above. -/
theorem iwasawaLieDecomp (n : ℕ) :
    Disjoint (KK n) (AA n) ∧ Disjoint (KK n) (NN n) ∧ Disjoint (AA n) (NN n)
    ∧ KK n ⊔ AA n ⊔ NN n = ⊤ :=
  ⟨disjoint_KK_AA n, disjoint_KK_NN n, disjoint_AA_NN n, iwasawa_codisjoint n⟩

/-- **Milestone 5 (f).** The Iwasawa Lie sum map: the linear-algebra
realization of the differential of `iwasawaMap` at the identity. -/
def iwasawaLieMap : (KK n × AA n × NN n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := fun p => p.1.1 + p.2.1.1 + p.2.2.1
  map_add' := fun ⟨X1, Y1, Z1⟩ ⟨X2, Y2, Z2⟩ => by
    show (X1.1 + X2.1) + (Y1.1 + Y2.1) + (Z1.1 + Z2.1) = (X1.1 + Y1.1 + Z1.1) + (X2.1 + Y2.1 + Z2.1)
    abel
  map_smul' := fun c ⟨X, Y, Z⟩ => by
    show c • X.1 + c • Y.1 + c • Z.1 = c • (X.1 + Y.1 + Z.1)
    rw [smul_add, smul_add]

/-- The Iwasawa Lie sum map is surjective: every matrix decomposes as
`M = K + A + N` (this is `iwasawa_codisjoint`). -/
theorem iwasawaLieMap_surjective : Function.Surjective (iwasawaLieMap (n := n)) := by
  intro M
  have h := iwasawa_codisjoint n
  have hMem : M ∈ KK n ⊔ AA n ⊔ NN n := by rw [h]; trivial
  rw [Submodule.mem_sup] at hMem
  obtain ⟨KA, hKA, N, hN, hsum⟩ := hMem
  rw [Submodule.mem_sup] at hKA
  obtain ⟨K, hK, A, hA, hKAsum⟩ := hKA
  refine ⟨(⟨K, hK⟩, ⟨A, hA⟩, ⟨N, hN⟩), ?_⟩
  show K + A + N = M
  rw [hKAsum, hsum]

/-- The Iwasawa Lie sum map is injective: if `X + Y + Z = 0` with
`X ∈ 𝔨, Y ∈ 𝔞, Z ∈ 𝔫`, then `X = Y = Z = 0`.

Entry-wise argument:
* For `i = j`: `X_{ii} = -X_{ii}` (skew) so `X_{ii} = 0`; `Z_{ii} = 0` (strict
  upper); hence `Y_{ii} = -X_{ii} - Z_{ii} = 0`.
* For `j < i` (below diagonal): `Y_{ij} = 0` (off-diag of diagonal),
  `Z_{ij} = 0` (`j ≤ i`); hence `X_{ij} = 0`.
* For `i < j` (above diagonal): apply the previous case at `(j, i)` to get
  `X_{ji} = 0`; skew gives `X_{ij} = -X_{ji} = 0`; then `Y_{ij} = 0`
  (off-diag) so `Z_{ij} = 0`. -/
theorem iwasawaLieMap_injective : Function.Injective (iwasawaLieMap (n := n)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩⟩ hker
  -- hker : iwasawaLieMap (...) = 0, i.e., X + Y + Z = 0
  have h : X + Y + Z = 0 := hker
  change X.transpose = -X at hX
  change ∀ i j, i ≠ j → Y i j = 0 at hY
  change ∀ i j, j ≤ i → Z i j = 0 at hZ
  have hentry : ∀ i j, X i j + Y i j + Z i j = 0 := fun i j => by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) h
    simpa using this
  have hSkew : ∀ i j, X j i = -X i j := fun i j => by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hX
    simpa using this
  -- X = 0 by trichotomy on (i, j).
  have hX0 : X = 0 := by
    ext i j
    simp only [Matrix.zero_apply]
    rcases lt_trichotomy j i with hji | hji | hji
    · -- j < i (below diagonal)
      have hYij : Y i j = 0 := hY i j (Ne.symm (ne_of_lt hji))
      have hZij : Z i j = 0 := hZ i j (le_of_lt hji)
      have := hentry i j
      linarith
    · -- j = i (diagonal): X i i = -X i i ⟹ X i i = 0
      rw [hji]
      have := hSkew i i
      linarith
    · -- i < j (above diagonal): use (j, i) and skew
      have hYji : Y j i = 0 := hY j i (Ne.symm (ne_of_lt hji))
      have hZji : Z j i = 0 := hZ j i (le_of_lt hji)
      have hjentry := hentry j i
      have hXji : X j i = 0 := by linarith
      have := hSkew i j
      rw [hXji] at this
      linarith
  -- With X = 0, h gives Y + Z = 0; entry-wise gives Y = 0, Z = 0.
  have hYZ0 : ∀ i j, Y i j + Z i j = 0 := fun i j => by
    have := hentry i j
    have hXij : X i j = 0 := by rw [hX0]; rfl
    linarith
  have hY0 : Y = 0 := by
    ext i j
    simp only [Matrix.zero_apply]
    rcases eq_or_ne i j with rfl | hij
    · have hZii : Z i i = 0 := hZ i i le_rfl
      have := hYZ0 i i
      linarith
    · exact hY i j hij
  have hZ0 : Z = 0 := by
    ext i j
    simp only [Matrix.zero_apply]
    have hYij : Y i j = 0 := by rw [hY0]; rfl
    have := hYZ0 i j
    linarith
  -- Conclude that the triple equals 0.
  show ((⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩) : KK n × AA n × NN n)
        = (0 : KK n × AA n × NN n)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact Subtype.ext hX0
  · exact Subtype.ext hY0
  · exact Subtype.ext hZ0

/-- **Milestone 5 (g): Iwasawa Lie isomorphism.** The sum map
`(X, Y, Z) ↦ X + Y + Z` is a linear equivalence from `𝔨 × 𝔞 × 𝔫` onto
`gl_n(ℝ)`. This is the algebraic content of "the differential of the
Iwasawa map at the identity is invertible," realized as a
`LinearEquiv`. The full `mfderiv` statement (relating this to the
geometric differential of `iwasawaMap`) additionally requires Milestone
3's smooth structures on `K n`, `A n`, `UU n`. -/
noncomputable def iwasawaLieEquiv :
    (KK n × AA n × NN n) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearEquiv.ofBijective iwasawaLieMap
    ⟨iwasawaLieMap_injective, iwasawaLieMap_surjective⟩

/-- Placeholder retained for compatibility with older notes. The real
manifold derivative statements are now proved in
`IwasawaMFDerivAtOne.lean` and `IwasawaMFDeriv.lean`; in particular,
`iwasawaMap_mfderiv_at_one_eq_lieEquiv` gives the identity-point
formula with the Cayley `-2` factor, and
`mfderiv_iwasawaMap_at_factored` gives the general-point formula. -/
theorem iwasawaMap_mfderiv_at_one : True := trivial

/-! ### Smooth structure on `UU n` (upper unipotent matrices)

`UU n` is an affine subset of `Matrix (Fin n) (Fin n) ℝ`: every upper
unipotent matrix has the form `1 + X` where `X` is strictly upper
triangular (i.e., `X ∈ NN n`). The map `U ↦ U - 1` provides a
homeomorphism `UU n ≃ₜ NN n`. We use this single chart, modeled on the
normed space `NN n`, to give `UU n` a smooth manifold structure via
`OpenPartialHomeomorph.singletonChartedSpace` and
`OpenPartialHomeomorph.isManifold_singleton`. -/

section SmoothUU

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

/-- For `U ∈ UU n`, the matrix `U - 1` is strictly upper triangular,
i.e., lies in `NN n`. -/
private lemma uu_sub_one_mem_NN (U : UU n) : U.1 - 1 ∈ NN n := by
  intro i j hji
  show U.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0
  rcases lt_or_eq_of_le hji with hlt | hji
  · -- j < i: U_{ij} = 0 (upper triangular), 1_{ij} = 0 (off-diagonal)
    rw [U.2.1 hlt, Matrix.one_apply_ne (ne_of_gt hlt)]
    ring
  · -- j = i: U_{ii} = 1 (unipotent), 1_{ii} = 1
    rw [hji, U.2.2 i, Matrix.one_apply_eq]
    ring

/-- For `X ∈ NN n`, the matrix `X + 1` is upper unipotent. -/
private lemma nn_add_one_isUpperUnipotent (X : NN n) : IsUpperUnipotent (X.1 + 1) := by
  refine ⟨?_, ?_⟩
  · -- Upper triangular: `(X + 1) i j = 0` when `j < i`.
    intro i j hij
    show X.1 i j + (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0
    have hX0 : X.1 i j = 0 := X.2 i j (le_of_lt hij)
    have hone : (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 :=
      Matrix.one_apply_ne (ne_of_gt hij)
    rw [hX0, hone]; ring
  · -- Diagonal entries equal 1: `X_{ii} = 0` (since `i ≤ i`), and `1_{ii} = 1`.
    intro i
    show X.1 i i + (1 : Matrix (Fin n) (Fin n) ℝ) i i = 1
    have hXii : X.1 i i = 0 := X.2 i i le_rfl
    rw [hXii, Matrix.one_apply_eq]; ring

/-- The homeomorphism `UU n ≃ₜ NN n` given by `U ↦ U - 1`. -/
def UU.toNNHomeomorph : UU n ≃ₜ NN n where
  toFun U := ⟨U.1 - 1, uu_sub_one_mem_NN U⟩
  invFun X := ⟨X.1 + 1, nn_add_one_isUpperUnipotent X⟩
  left_inv := fun U => Subtype.ext (sub_add_cancel _ _)
  right_inv := fun X => Subtype.ext (add_sub_cancel_right _ _)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.add continuous_const

/-- Smooth manifold structure on `UU n`, modeled on the normed space `NN n`. -/
noncomputable instance instChartedSpaceUU :
    ChartedSpace (NN n) (UU n) :=
  OpenPartialHomeomorph.singletonChartedSpace
    (UU.toNNHomeomorph.toOpenPartialHomeomorph) (by simp)

instance instIsManifoldUU :
    IsManifold (𝓘(ℝ, (NN n : Type _))) ⊤ (UU n) :=
  OpenPartialHomeomorph.isManifold_singleton
    (UU.toNNHomeomorph.toOpenPartialHomeomorph) (by simp)

end SmoothUU

/-! ### Smooth structure on `A n` (positive diagonal matrices)

`A n` is the positive diagonal matrices. The map `D ↦ (log D_{ii})_i`
gives a homeomorphism `A n ≃ₜ (Fin n → ℝ)` (with inverse `v ↦ diag(exp v)`).
We use this single chart, modeled on `Fin n → ℝ`, to give `A n` a
smooth manifold structure. -/

section SmoothA

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

/-- For `v : Fin n → ℝ`, the diagonal matrix with entries `exp(v i)` is
positive diagonal. -/
private lemma exp_diag_isPositiveDiagonal (v : Fin n → ℝ) :
    IsPositiveDiagonal (Matrix.diagonal (fun i => Real.exp (v i))) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · intro i
    rw [Matrix.diagonal_apply_eq]
    exact Real.exp_pos _

/-- Homeomorphism `A n ≃ₜ (Fin n → ℝ)` via `D ↦ (log D_{ii})_i`. -/
noncomputable def A.toFinNRHomeomorph : A n ≃ₜ (Fin n → ℝ) where
  toFun D := fun i => Real.log (D.1 i i)
  invFun v := ⟨Matrix.diagonal (fun i => Real.exp (v i)),
                exp_diag_isPositiveDiagonal v⟩
  left_inv := fun D => by
    apply Subtype.ext
    show Matrix.diagonal (fun i => Real.exp (Real.log (D.1 i i))) = D.1
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Real.exp_log (D.2.2 i)]
    · rw [Matrix.diagonal_apply_ne _ hij, D.2.1 i j hij]
  right_inv := fun v => by
    funext i
    show Real.log (Matrix.diagonal (fun i => Real.exp (v i)) i i) = v i
    rw [Matrix.diagonal_apply_eq, Real.log_exp]
  continuous_toFun := by
    refine continuous_pi (fun i => ?_)
    refine Continuous.log ?_ (fun D => ne_of_gt (D.2.2 i))
    exact (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine Continuous.matrix_diagonal ?_
    exact continuous_pi (fun i => Real.continuous_exp.comp (continuous_apply i))

/-- Smooth manifold structure on `A n`, modeled on `Fin n → ℝ`. -/
noncomputable instance instChartedSpaceA :
    ChartedSpace (Fin n → ℝ) (A n) :=
  OpenPartialHomeomorph.singletonChartedSpace
    (A.toFinNRHomeomorph.toOpenPartialHomeomorph) (by simp)

instance instIsManifoldA :
    IsManifold (𝓘(ℝ, (Fin n → ℝ))) ⊤ (A n) :=
  OpenPartialHomeomorph.isManifold_singleton
    (A.toFinNRHomeomorph.toOpenPartialHomeomorph) (by simp)

end SmoothA

/-! ### The Cayley transform: skew-symmetric ↔ orthogonal

The Cayley transform `X ↦ (1 − X)(1 + X)⁻¹` provides a parametrization of
`O(n)` minus a measure-zero set by skew-symmetric matrices `Sk n = 𝔨`.
For `X` skew, `1 + X` is invertible (its real eigenvalues are 1, complex
ones are `1 ± iλ` of modulus `√(1 + λ²) > 0`), so the formula is defined
on all of `Sk n`. The image lands in the open subset of `K n` where
`1 + Q` is invertible (i.e., where `−1` is not an eigenvalue of `Q`).

This gives a key chart toward a smooth manifold structure on `K n = O(n)`,
following the standard Cayley-transform parametrization. The full atlas
on all of `O(n)` requires additional charts (translates of Cayley by
fixed elements of `O(n)`); we lay the groundwork here.

References:
* Cayley, A. (1846). "Sur quelques propriétés des déterminants gauches."
* Postnikov, *Lectures in Geometry V: Lie Groups and Lie Algebras* (1986).
-/

section CayleyTransform

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

/-- The Cayley transform `X ↦ (1 − X)(1 + X)⁻¹` (matrix-valued, on all of
`Matrix (Fin n) (Fin n) ℝ` though only useful when `1 + X` is invertible). -/
noncomputable def cayley (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 - X) * (1 + X)⁻¹

/-- Inverse Cayley transform `Q ↦ (1 − Q)(1 + Q)⁻¹` (same formula in
matrix entries; for `Q` in the appropriate open set, returns a
skew-symmetric matrix). -/
noncomputable def cayleyInv (Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 - Q) * (1 + Q)⁻¹

/-- For a skew-symmetric matrix `X` over the reals, `1 + X` is invertible.

Proof: `(1 + X)(1 − X) = 1 − X² = 1 + X · Xᵀ` (using `Xᵀ = −X` for skew `X`).
The matrix `X · Xᵀ` is positive semi-definite (general fact for real
matrices), so `1 + X · Xᵀ` is positive definite, hence has positive
determinant. Then `det(1 + X)·det(1 − X) > 0`; using
`det(1 − X) = det((1 + X)ᵀ) = det(1 + X)`, we get `det(1 + X)² > 0`,
so `det(1 + X) ≠ 0`. The `n = 0` case is trivial since the empty
determinant equals `1`. -/
theorem one_add_skew_isUnit (X : Sk n) : IsUnit ((1 + X.1).det) := by
  have hX : X.1.transpose = -X.1 := X.2
  rcases isEmpty_or_nonempty (Fin n) with hempty | hnonempty
  · -- n = 0: empty determinant is 1.
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  · -- n ≥ 1: positive-definiteness argument.
    -- (1 + X)(1 - X) = 1 + X · Xᵀ
    have hMul : (1 + X.1) * (1 - X.1) = 1 + X.1 * X.1.transpose := by
      rw [hX]
      noncomm_ring
    -- 1 + X · Xᵀ is positive definite (1 is PosDef + X·Xᵀ is PosSemidef)
    have hPosDef : Matrix.PosDef (1 + X.1 * X.1.transpose) := by
      refine Matrix.PosDef.add_posSemidef ?_ ?_
      · -- 1 is positive definite
        rw [show (1 : Matrix (Fin n) (Fin n) ℝ) = ((1 : ℕ) : Matrix (Fin n) (Fin n) ℝ) from
              by simp]
        exact (Matrix.posDef_natCast_iff).mpr one_pos
      · -- X · Xᵀ is positive semi-definite (transpose = conjTranspose for ℝ).
        have heq : X.1.transpose = X.1.conjTranspose := by
          ext i j
          simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
        rw [heq]
        exact Matrix.posSemidef_self_mul_conjTranspose X.1
    -- (1 + X) * (1 - X) is invertible (PosDef → IsUnit)
    have hUnitMul : IsUnit ((1 + X.1) * (1 - X.1)) := by
      rw [hMul]
      exact hPosDef.isUnit
    -- Hence 1 + X is invertible (factor of an invertible)
    have hUnit : IsUnit (1 + X.1) := isUnit_of_mul_isUnit_left hUnitMul
    exact (Matrix.isUnit_iff_isUnit_det _).mp hUnit

/-- For `X : Sk n`, the Cayley transform `cayley X = (1 − X)(1 + X)⁻¹` lands
in the orthogonal group `K n`. -/
theorem cayley_isOrthogonal (X : Sk n) : IsOrthogonal (cayley X.1) := by
  have hX : X.1.transpose = -X.1 := X.2
  -- Setup invertibility facts
  have h_1pX_det : IsUnit (1 + X.1).det := one_add_skew_isUnit X
  have h_1pX : IsUnit (1 + X.1) := (Matrix.isUnit_iff_isUnit_det _).mpr h_1pX_det
  -- -X is also skew, so 1 - X = 1 + (-X) is invertible.
  have h_negX_skew : (-X.1).transpose = -(-X.1) := by rw [Matrix.transpose_neg, hX]
  have h_1mX_det : IsUnit (1 - X.1).det := by
    rw [show (1 - X.1) = 1 + (-X.1) from by abel]
    exact one_add_skew_isUnit ⟨-X.1, h_negX_skew⟩
  -- Transpose identities for X skew
  have hT_1pX : (1 + X.1).transpose = 1 - X.1 := by
    rw [Matrix.transpose_add, Matrix.transpose_one, hX, ← sub_eq_add_neg]
  have hT_1mX : (1 - X.1).transpose = 1 + X.1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hX, sub_neg_eq_add]
  -- (cayley X)ᵀ = (1 − X)⁻¹ · (1 + X)
  have hCayleyT : (cayley X.1).transpose = (1 - X.1)⁻¹ * (1 + X.1) := by
    unfold cayley
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hT_1pX, hT_1mX]
  -- (1 + X)(1 − X) = (1 − X)(1 + X), hence the inverses commute.
  have hComm : (1 + X.1) * (1 - X.1) = (1 - X.1) * (1 + X.1) := by noncomm_ring
  have hCommInv : (1 + X.1)⁻¹ * (1 - X.1)⁻¹ = (1 - X.1)⁻¹ * (1 + X.1)⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← hComm, Matrix.mul_inv_rev]
  -- Goal: cayley X * (cayley X)ᵀ = 1.
  show cayley X.1 * (cayley X.1).transpose = 1
  rw [hCayleyT]
  unfold cayley
  -- (1 − X)·(1 + X)⁻¹ · (1 − X)⁻¹ · (1 + X) = 1.
  calc (1 - X.1) * (1 + X.1)⁻¹ * ((1 - X.1)⁻¹ * (1 + X.1))
      = (1 - X.1) * ((1 + X.1)⁻¹ * (1 - X.1)⁻¹) * (1 + X.1) := by noncomm_ring
    _ = (1 - X.1) * ((1 - X.1)⁻¹ * (1 + X.1)⁻¹) * (1 + X.1) := by rw [hCommInv]
    _ = (1 - X.1) * (1 - X.1)⁻¹ * ((1 + X.1)⁻¹ * (1 + X.1)) := by noncomm_ring
    _ = 1 * 1 := by
        rw [Matrix.mul_nonsing_inv _ h_1mX_det, Matrix.nonsing_inv_mul _ h_1pX_det]
    _ = 1 := one_mul _

/-- The Cayley transform as a function from `Sk n` (skew-symmetric matrices)
into `K n` (orthogonal matrices). The image consists of orthogonal matrices
`Q` such that `1 + Q` is invertible (i.e., `−1` is not an eigenvalue),
which is an open dense subset of `K n`. -/
noncomputable def cayleyToK (X : Sk n) : K n :=
  ⟨cayley X.1, cayley_isOrthogonal X⟩

/-- Key identity: `(1 + cayley X) · (1 + X) = 1 + 1` for any `X` with
`1 + X` invertible. This is what makes the Cayley transform a self-inverse
formula. -/
private lemma one_add_cayley_mul (X : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + X).det) :
    (1 + cayley X) * (1 + X) = 1 + 1 := by
  unfold cayley
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  show (1 + X) + (1 - X) = 1 + 1
  noncomm_ring

/-- Companion identity: `(1 − cayley X) · (1 + X) = X + X`. -/
private lemma one_sub_cayley_mul (X : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + X).det) :
    (1 - cayley X) * (1 + X) = X + X := by
  unfold cayley
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ h, Matrix.mul_one]
  show (1 + X) - (1 - X) = X + X
  noncomm_ring

/-- `1 + cayley X` is invertible whenever `1 + X` is. -/
private lemma one_add_cayley_isUnit (X : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + X).det) :
    IsUnit ((1 + cayley X).det) := by
  -- From `(1 + cayley X) · (1 + X) = 1 + 1`, det((1+1)) = 2^n ≠ 0.
  have hMul := one_add_cayley_mul X h
  have hDet : (1 + cayley X).det * (1 + X).det
              = (1 + 1 : Matrix (Fin n) (Fin n) ℝ).det := by
    rw [← Matrix.det_mul, hMul]
  -- det(1 + 1 : Matrix) = 2^n
  have hDet11 : ((1 + 1 : Matrix (Fin n) (Fin n) ℝ).det) = (2 : ℝ)^n := by
    rw [show (1 + 1 : Matrix (Fin n) (Fin n) ℝ) = (2 : ℝ) • 1 from by
          ext i j
          rcases eq_or_ne i j with rfl | hij
          · simp [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply]
            norm_num
          · simp [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.smul_apply]]
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [hDet11] at hDet
  -- (1 + cayley X).det · (1 + X).det = 2^n, both factors must be units.
  have h2n_unit : IsUnit ((2 : ℝ)^n) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)
  rw [← hDet] at h2n_unit
  exact (IsUnit.mul_iff.mp h2n_unit).1

/-- **General self-inverse property.** `cayley` (= `cayleyInv` as a formula)
is its own inverse on the open set of matrices `M` with `1 + M` invertible:
`cayley (cayley M) = M` for any such `M`. The proof uses the algebraic
identities `(1 + cayley M)(1 + M) = 1 + 1` and `(1 − cayley M)(1 + M) = M + M`
to derive `(1 − cayley M) = M · (1 + cayley M)`, then cancels. -/
theorem cayley_self_inverse (X : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + X).det) : cayley (cayley X) = X := by
  have h_1pCay_det : IsUnit (1 + cayley X).det := one_add_cayley_isUnit X h
  -- Strategy: show (1 - cayley X) = X · (1 + cayley X), then divide by (1 + cayley X).
  have hKey : 1 - cayley X = X * (1 + cayley X) := by
    have lhsMul : (1 - cayley X) * (1 + X) = X + X := one_sub_cayley_mul X h
    have rhsMul : X * (1 + cayley X) * (1 + X) = X + X := by
      rw [Matrix.mul_assoc, one_add_cayley_mul X h]
      noncomm_ring
    -- Cancel (1 + X) from the right: both sides equal when post-multiplied by (1 + X),
    -- and (1 + X) is invertible.
    have heq : (1 - cayley X) * (1 + X) = X * (1 + cayley X) * (1 + X) := by
      rw [lhsMul, rhsMul]
    have := congrArg (· * (1 + X)⁻¹) heq
    simp only at this
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one] at this
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h,
        Matrix.mul_one] at this
    exact this
  -- From hKey: cayley (cayley X) = (1 - cayley X)(1 + cayley X)⁻¹
  --                              = X · (1 + cayley X) · (1 + cayley X)⁻¹ = X.
  show (1 - cayley X) * (1 + cayley X)⁻¹ = X
  rw [hKey, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h_1pCay_det, Matrix.mul_one]

/-- **Left inverse.** `cayleyInv ∘ cayley = id` on skew-symmetric matrices.

Specialization of `cayley_self_inverse` to `Sk n` (using
`one_add_skew_isUnit` to discharge the invertibility hypothesis). -/
theorem cayleyInv_cayley (X : Sk n) : cayleyInv (cayley X.1) = X.1 :=
  cayley_self_inverse X.1 (one_add_skew_isUnit X)

/-- **Right inverse.** `cayley ∘ cayleyInv = id` on the open subset of matrices
where `1 + Q` is invertible. (Since `cayley` and `cayleyInv` are the same
formula, this is the same statement as `cayleyInv_cayley`, but specialized
to a different input domain.) -/
theorem cayley_cayleyInv (Q : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + Q).det) : cayley (cayleyInv Q) = Q :=
  cayley_self_inverse Q h

/-- **`cayleyInv Q` is skew-symmetric** for orthogonal `Q` with `1 + Q`
invertible. The proof uses orthogonality (`Qᵀ = Q⁻¹`) and the algebraic
manipulation `(1 + Q⁻¹) = Q⁻¹ · (Q + 1)` to relate `(cayleyInv Q)ᵀ`
to `−cayleyInv Q`. -/
theorem cayleyInv_isSkew (Q : Matrix (Fin n) (Fin n) ℝ)
    (hOrth : IsOrthogonal Q) (h : IsUnit (1 + Q).det) :
    (cayleyInv Q).transpose = -(cayleyInv Q) := by
  -- Step 1: Q is invertible, with Q⁻¹ = Qᵀ.
  have hQ_unit : IsUnit Q := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    exact isUnit_iff_ne_zero.mpr hOrth.det_ne_zero
  have hQinv : Q⁻¹ = Q.transpose := hOrth.matInv_eq_transpose
  have hQ_det : IsUnit Q.det := isUnit_iff_ne_zero.mpr hOrth.det_ne_zero
  -- Step 2: 1 - Q is also invertible. Use `Matrix.IsHermitian` reasoning?
  -- Actually we don't need this; we'll work directly.
  -- Step 3: Compute (cayleyInv Q)ᵀ.
  unfold cayleyInv
  -- ((1 - Q) * (1 + Q)⁻¹).transpose = ((1 + Q)⁻¹).transpose * (1 - Q).transpose
  --                                 = ((1 + Q).transpose)⁻¹ * (1 - Qᵀ)
  --                                 = (1 + Qᵀ)⁻¹ * (1 - Qᵀ)
  -- For Q orthogonal, Qᵀ = Q⁻¹.
  -- = (1 + Q⁻¹)⁻¹ * (1 - Q⁻¹)
  -- = (Q · (Q + 1)⁻¹) * (-(1 - Q) · Q⁻¹)         [using (1 + Q⁻¹) = (Q + 1) · Q⁻¹]
  -- = -Q * (1 + Q)⁻¹ * (1 - Q) * Q⁻¹
  -- Q commutes with (1 - Q), (1 + Q), and their inverses (all polynomials in Q).
  -- So = -(1 - Q) * (1 + Q)⁻¹ * Q * Q⁻¹ = -(1 - Q) * (1 + Q)⁻¹ = -cayleyInv Q.
  -- Direct manipulation in Lean:
  have h_T_1pQ : (1 + Q).transpose = 1 + Q.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
  have h_T_1mQ : (1 - Q).transpose = 1 - Q.transpose := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
  -- (cayleyInv Q)ᵀ = (1 + Q.transpose)⁻¹ * (1 - Q.transpose)
  have hTrans : ((1 - Q) * (1 + Q)⁻¹).transpose
              = (1 + Q.transpose)⁻¹ * (1 - Q.transpose) := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, h_T_1pQ, h_T_1mQ]
  rw [hTrans]
  -- Substitute Qᵀ = Q⁻¹
  rw [← hQinv]
  -- Goal: (1 + Q⁻¹)⁻¹ * (1 - Q⁻¹) = -((1 - Q) * (1 + Q)⁻¹)
  -- Multiply both sides by (1 + Q) on the right; cancel.
  -- LHS · (1 + Q) = (1 + Q⁻¹)⁻¹ * (1 - Q⁻¹) * (1 + Q).
  -- (1 - Q⁻¹) * (1 + Q) = (1 + Q) - Q⁻¹ * (1 + Q) = (1 + Q) - (Q⁻¹ + 1) = Q - Q⁻¹.
  -- (1 + Q⁻¹)⁻¹ * (Q - Q⁻¹) = ?
  --
  -- Cleaner: multiply both sides by Q on the left.
  -- Q · (1 + Q⁻¹) = Q + 1, so Q⁻¹ · (Q + 1)⁻¹ ... hmm.
  -- Actually: (1 + Q⁻¹) = Q⁻¹(Q + 1) = Q⁻¹(1 + Q). So (1 + Q⁻¹)⁻¹ = (1 + Q)⁻¹ · Q.
  have h_inv_eq : (1 + Q⁻¹)⁻¹ = (1 + Q)⁻¹ * Q := by
    -- (1 + Q⁻¹) = Q⁻¹ · (Q + 1) = Q⁻¹ · (1 + Q)
    have h_decomp : 1 + Q⁻¹ = Q⁻¹ * (1 + Q) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.nonsing_inv_mul _ hQ_det]
      abel
    rw [h_decomp, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ hQ_det]
  rw [h_inv_eq]
  -- Goal: (1 + Q)⁻¹ * Q * (1 - Q⁻¹) = -((1 - Q) * (1 + Q)⁻¹)
  -- Compute Q * (1 - Q⁻¹) = Q - Q · Q⁻¹ = Q - 1 = -(1 - Q).
  have h_QmulSub : Q * (1 - Q⁻¹) = -(1 - Q) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_nonsing_inv _ hQ_det]
    noncomm_ring
  rw [Matrix.mul_assoc, h_QmulSub]
  -- Goal: (1 + Q)⁻¹ * (-(1 - Q)) = -((1 - Q) * (1 + Q)⁻¹)
  -- = -(1 + Q)⁻¹ * (1 - Q) = -((1 - Q) * (1 + Q)⁻¹)
  -- Need commutativity of (1 - Q) and (1 + Q)⁻¹ — they commute since both are polynomials in Q.
  have h_comm : (1 + Q)⁻¹ * (1 - Q) = (1 - Q) * (1 + Q)⁻¹ := by
    -- (1 - Q)(1 + Q) = (1 + Q)(1 - Q) gives commutativity of inverses too.
    have h_polycomm : (1 - Q) * (1 + Q) = (1 + Q) * (1 - Q) := by noncomm_ring
    -- Show (1 + Q)⁻¹ * (1 - Q) * (1 + Q) = 1 - Q using h_polycomm.
    have hStep : (1 + Q)⁻¹ * (1 - Q) * (1 + Q) = 1 - Q := by
      rw [Matrix.mul_assoc, h_polycomm, ← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
    -- Multiply on the right by (1 + Q)⁻¹:
    have := congrArg (· * (1 + Q)⁻¹) hStep
    simp only at this
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one] at this
    exact this
  rw [Matrix.mul_neg, h_comm]

/-- The open subset of `K n` (orthogonal matrices) consisting of those `Q`
with `1 + Q` invertible (equivalently, `−1` is not an eigenvalue of `Q`).
This is the image of `Sk n` under the Cayley transform. -/
abbrev K_open (n : ℕ) : Type :=
  { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q ∧ IsUnit (1 + Q).det }

/-- **The Cayley equivalence.** The Cayley transform gives a bijection
between skew-symmetric matrices `Sk n` and the open subset
`K_open n` of orthogonal matrices `Q` with `1 + Q` invertible. -/
noncomputable def cayleyEquiv : (Sk n) ≃ K_open n where
  toFun X := ⟨cayley X.1,
              cayley_isOrthogonal X,
              one_add_cayley_isUnit X.1 (one_add_skew_isUnit X)⟩
  invFun Q := ⟨cayleyInv Q.1, cayleyInv_isSkew Q.1 Q.2.1 Q.2.2⟩
  left_inv := fun X => Subtype.ext (cayleyInv_cayley X)
  right_inv := fun Q => Subtype.ext (cayley_cayleyInv Q.1 Q.2.2)

/-! ### Continuity of the Cayley transform

The Cayley transform `X ↦ (1 − X)(1 + X)⁻¹` is continuous on the open
set where `1 + X` is invertible. We use Mathlib's `continuousAt_matrix_inv`
(via `NormedRing.inverse_continuousAt` for `Ring.inverse` continuity at
units). -/

/-- Continuity of the Cayley transform on the subtype of skew-symmetric
matrices. -/
theorem continuous_cayley_on_skew :
    Continuous (fun X : Sk n => cayley X.1) := by
  unfold cayley
  -- (1 - X) * (1 + X)⁻¹: product of continuous functions.
  refine Continuous.mul ?_ ?_
  · -- 1 - X continuous (subtraction of continuous functions).
    exact continuous_const.sub continuous_subtype_val
  · -- (1 + X)⁻¹ continuous via continuousAt at each X.
    rw [continuous_iff_continuousAt]
    intro X
    have hAdd : ContinuousAt (fun Y : Sk n => (1 + Y.1 : Matrix (Fin n) (Fin n) ℝ)) X :=
      (continuous_const.add continuous_subtype_val).continuousAt
    have hUnitDet : IsUnit ((1 + X.1).det) := one_add_skew_isUnit X
    have hRingInv : ContinuousAt Ring.inverse ((1 + X.1).det) :=
      NormedRing.inverse_continuousAt hUnitDet.unit
    have hMatInv : ContinuousAt Inv.inv (1 + X.1) :=
      continuousAt_matrix_inv (1 + X.1) hRingInv
    exact ContinuousAt.comp (g := Inv.inv) (f := fun Y : Sk n => 1 + Y.1) hMatInv hAdd

/-- Continuity of `cayleyInv` on the open subset of `Matrix` where `1 + Q`
is invertible (in particular, on `K_open n`). -/
theorem continuous_cayleyInv_on_KOpen :
    Continuous (fun Q : K_open n => cayleyInv Q.1) := by
  unfold cayleyInv
  refine Continuous.mul ?_ ?_
  · exact continuous_const.sub continuous_subtype_val
  · rw [continuous_iff_continuousAt]
    intro Q
    have hAdd : ContinuousAt (fun Q' : K_open n => (1 + Q'.1 : Matrix (Fin n) (Fin n) ℝ)) Q :=
      (continuous_const.add continuous_subtype_val).continuousAt
    have hUnitDet : IsUnit ((1 + Q.1).det) := Q.2.2
    have hRingInv : ContinuousAt Ring.inverse ((1 + Q.1).det) :=
      NormedRing.inverse_continuousAt hUnitDet.unit
    have hMatInv : ContinuousAt Inv.inv (1 + Q.1) :=
      continuousAt_matrix_inv (1 + Q.1) hRingInv
    exact ContinuousAt.comp (g := Inv.inv) (f := fun Q' : K_open n => 1 + Q'.1) hMatInv hAdd

/-- **The Cayley homeomorphism.** The Cayley transform is a homeomorphism
between skew-symmetric matrices `Sk n` and the open subset `K_open n` of
orthogonal matrices with `1 + Q` invertible. -/
noncomputable def cayleyHomeomorph : (Sk n) ≃ₜ K_open n where
  toEquiv := cayleyEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_cayley_on_skew
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_cayleyInv_on_KOpen

/-- `K_open n` is nonempty: the identity matrix `1` is orthogonal and has
`1 + 1 = 2 · 1` invertible (det = `2^n`). -/
instance : Nonempty (K_open n) := by
  refine ⟨⟨1, ?_, ?_⟩⟩
  · -- IsOrthogonal 1: 1 · 1ᵀ = 1
    show (1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ).transpose = 1
    rw [Matrix.transpose_one, Matrix.one_mul]
  · -- IsUnit (1 + 1).det
    have hDet11 : ((1 + 1 : Matrix (Fin n) (Fin n) ℝ).det) = (2 : ℝ)^n := by
      rw [show (1 + 1 : Matrix (Fin n) (Fin n) ℝ) = (2 : ℝ) • 1 from by
            ext i j
            rcases eq_or_ne i j with rfl | hij
            · simp [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply]
              norm_num
            · simp [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.smul_apply]]
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [hDet11]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)

/-- The inverse Cayley transform is an open embedding `K_open n ↪ Sk n`. -/
theorem cayleyInv_isOpenEmbedding :
    IsOpenEmbedding (cayleyHomeomorph.symm : K_open n → Sk n) :=
  cayleyHomeomorph.symm.isOpenEmbedding

/-- Smooth manifold structure on `K_open n` (the open subset of `O(n)`
where `1 + Q` is invertible), modeled on the normed space `Sk n` of
skew-symmetric matrices. The chart is the inverse Cayley transform. -/
noncomputable instance instChartedSpaceKOpen :
    ChartedSpace (Sk n) (K_open n) :=
  cayleyInv_isOpenEmbedding.singletonChartedSpace

instance instIsManifoldKOpen :
    IsManifold (𝓘(ℝ, (Sk n : Type _))) ⊤ (K_open n) :=
  cayleyInv_isOpenEmbedding.isManifold_singleton (I := 𝓘(ℝ, (Sk n : Type _))) (n := ⊤)

/-- The chart `cayleyHomeomorph.symm : K_open n → Sk n` is `C∞`. -/
theorem contMDiff_cayleyHomeomorphSymm :
    ContMDiff (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _))) ⊤
      (cayleyHomeomorph.symm : K_open n → Sk n) :=
  contMDiff_isOpenEmbedding (I := 𝓘(ℝ, (Sk n : Type _))) (n := ⊤) cayleyInv_isOpenEmbedding

/-- The forward Cayley map `cayleyHomeomorph : Sk n → K_open n` is `C∞`.

Uses `contMDiffOn_isOpenEmbedding_symm` (smoothness of the inverse chart
on its target) plus surjectivity of `cayleyHomeomorph.symm`. The
function-level identification `(toOpenPartialHomeomorph _).symm = cayleyHomeomorph`
follows from the left-inverse property of `IsOpenEmbedding.toOpenPartialHomeomorph`. -/
theorem contMDiff_cayleyHomeomorph :
    ContMDiff (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _))) ⊤
      (cayleyHomeomorph : Sk n → K_open n) := by
  have h_smooth_on :
      ContMDiffOn (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _))) ⊤
        (cayleyInv_isOpenEmbedding.toOpenPartialHomeomorph
          (cayleyHomeomorph.symm : K_open n → Sk n)).symm
        (Set.range (cayleyHomeomorph.symm : K_open n → Sk n)) :=
    contMDiffOn_isOpenEmbedding_symm
      (I := 𝓘(ℝ, (Sk n : Type _))) (n := ⊤) cayleyInv_isOpenEmbedding
  have h_range : Set.range (cayleyHomeomorph.symm : K_open n → Sk n) = Set.univ :=
    cayleyHomeomorph.symm.surjective.range_eq
  rw [h_range, contMDiffOn_univ] at h_smooth_on
  have heq :
      (cayleyInv_isOpenEmbedding.toOpenPartialHomeomorph
          (cayleyHomeomorph.symm : K_open n → Sk n)).symm
        = (cayleyHomeomorph : Sk n → K_open n) := by
    funext x
    -- Set Y = cayleyHomeomorph x. Then cayleyHomeomorph.symm Y = x.
    -- By the left-inverse lemma, `(...).symm (cayleyHomeomorph.symm Y) = Y = cayleyHomeomorph x`.
    have hY : cayleyHomeomorph.symm (cayleyHomeomorph x) = x := cayleyHomeomorph.left_inv x
    conv_lhs => rw [← hY]
    exact cayleyInv_isOpenEmbedding.toOpenPartialHomeomorph_left_inv
  rw [heq] at h_smooth_on
  exact h_smooth_on

/-- **The Cayley diffeomorphism.** The Cayley transform is a `C∞` diffeomorphism
between skew-symmetric matrices `Sk n` and the open subset `K_open n` of
orthogonal matrices with `1 + Q` invertible. -/
noncomputable def cayleyDiffeomorph :
    Diffeomorph (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _))) (Sk n) (K_open n) ⊤ where
  toEquiv := cayleyEquiv
  contMDiff_toFun := contMDiff_cayleyHomeomorph
  contMDiff_invFun := contMDiff_cayleyHomeomorphSymm

/-! ### Translated Cayley charts (toward a multi-chart atlas on `K n`)

Following Mathlib's pattern for `Mathlib.Geometry.Manifold.Instances.Sphere`
(stereographic projection from each unit vector), we use a Cayley chart
centered at *every* point `Q₀ ∈ K n`. The chart at `Q₀` is the bijection
`X ↦ cayley X · Q₀` from `Sk n` to the translate `K_open · Q₀` of the
identity-centered open set. The atlas `{cayleyChartAt Q₀ | Q₀ ∈ K n}`
covers all of `K n`: any `Q ∈ K n` is in the source of `cayleyChartAt Q`
because `1 + Q · Q.transpose = 1 + 1 = 2` is invertible. -/

/-- The product of two orthogonal matrices is orthogonal. -/
theorem IsOrthogonal.mul {Q R : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonal Q) (hR : IsOrthogonal R) : IsOrthogonal (Q * R) := by
  show (Q * R) * (Q * R).transpose = 1
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hR, Matrix.mul_one]
  exact hQ

/-- The open subset `K_open · Q₀` of `K n`: orthogonal matrices `Q` such that
`Q · Q₀.transpose ∈ K_open` (equivalently, `1 + Q · Q₀.transpose` is
invertible — `−1` is not an eigenvalue of `Q · Q₀⁻¹`). -/
abbrev K_open_at (Q₀ : K n) : Type :=
  { Q : Matrix (Fin n) (Fin n) ℝ //
      IsOrthogonal Q ∧ IsUnit (1 + Q * Q₀.1.transpose).det }

/-- The Cayley equivalence centered at `Q₀ ∈ K n`. The forward map is
`X ↦ cayley X · Q₀` (orthogonal because both factors are); the inverse
is `Q ↦ cayleyInv (Q · Q₀.transpose)` (skew because `Q · Q₀.transpose`
is orthogonal). The two-sided inverse property reduces to the
identity-centered case via right-multiplication by `Q₀`. -/
noncomputable def cayleyEquivAt (Q₀ : K n) : (Sk n) ≃ K_open_at Q₀ where
  toFun X :=
    ⟨cayley X.1 * Q₀.1,
     IsOrthogonal.mul (cayley_isOrthogonal X) Q₀.2,
     by
       -- `1 + (cayley X · Q₀) · Q₀.transpose = 1 + cayley X · (Q₀ · Q₀.transpose)
       --                                     = 1 + cayley X · 1 = 1 + cayley X`,
       -- which is invertible by `one_add_cayley_isUnit`.
       have hQ₀ : Q₀.1 * Q₀.1.transpose = 1 := Q₀.2
       have : (cayley X.1 * Q₀.1) * Q₀.1.transpose = cayley X.1 := by
         rw [Matrix.mul_assoc, hQ₀, Matrix.mul_one]
       rw [this]
       exact one_add_cayley_isUnit X.1 (one_add_skew_isUnit X)⟩
  invFun Q :=
    -- Q · Q₀.transpose is orthogonal (product of orthogonals), with
    -- 1 + Q · Q₀.transpose invertible (= Q.2.2). Apply cayleyEquiv.symm.
    cayleyEquiv.symm ⟨Q.1 * Q₀.1.transpose,
                      IsOrthogonal.mul Q.2.1 (IsOrthogonal.transpose Q₀.2), Q.2.2⟩
  left_inv := fun X => by
    -- Compute: cayleyEquiv.symm (cayley X · Q₀ · Q₀.transpose, ...) = cayleyEquiv.symm (cayley X, ...) = X.
    apply Subtype.ext
    have hQ₀ : Q₀.1 * Q₀.1.transpose = 1 := Q₀.2
    -- Unfold cayleyEquiv.symm: it returns ⟨cayleyInv ?.1, _⟩.
    show cayleyInv ((cayley X.1 * Q₀.1) * Q₀.1.transpose) = X.1
    rw [Matrix.mul_assoc, hQ₀, Matrix.mul_one]
    exact cayleyInv_cayley X
  right_inv := fun Q => by
    -- Compute: cayley (cayleyInv (Q · Q₀.transpose)) · Q₀ = (Q · Q₀.transpose) · Q₀ = Q.
    apply Subtype.ext
    have hQ₀ : Q₀.1.transpose * Q₀.1 = 1 := mul_eq_one_comm.mp Q₀.2
    -- Unfold cayleyEquiv.symm and the toFun.
    show cayley (cayleyInv (Q.1 * Q₀.1.transpose)) * Q₀.1 = Q.1
    rw [cayley_cayleyInv _ Q.2.2]
    rw [Matrix.mul_assoc, hQ₀, Matrix.mul_one]

/-- For any `Q ∈ K n`, the Cayley chart `cayleyEquivAt Q` (centered at `Q`)
contains `Q` itself in its codomain image: `Q ∈ K_open_at Q`. This is
because `Q · Q.transpose = 1` and `1 + 1` has invertible determinant
(`= 2^n ≠ 0`). This is the key fact making the chart-at-every-point
atlas cover all of `K n`. -/
theorem self_mem_K_open_at (Q : K n) :
    IsUnit ((1 + Q.1 * Q.1.transpose).det) := by
  have hQQT : Q.1 * Q.1.transpose = 1 := Q.2
  rw [hQQT]
  -- IsUnit (1 + 1).det = 2^n
  have hDet11 : ((1 + 1 : Matrix (Fin n) (Fin n) ℝ).det) = (2 : ℝ)^n := by
    rw [show (1 + 1 : Matrix (Fin n) (Fin n) ℝ) = (2 : ℝ) • 1 from by
          ext i j
          rcases eq_or_ne i j with rfl | hij
          · simp [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply]
            norm_num
          · simp [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.smul_apply]]
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [hDet11]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)

/-! ### Open partial homeomorphisms and charts on the full orthogonal group

To avoid defining the Cayley formula globally off its natural source, we
first restrict `K n` to the open subset where the translated Cayley
chart at `Q₀` is defined, build a genuine homeomorphism from that open
subtype to `Sk n`, and then compose with the subtype inclusion viewed as
an `OpenPartialHomeomorph`. This packages each translated Cayley chart as
an `OpenPartialHomeomorph (K n) (Sk n)` without any off-source branching. -/

/-- The source of the translated Cayley chart at `Q₀`, viewed as an open subset of `K n`. -/
private def cayleySourceAt (Q₀ : K n) : TopologicalSpace.Opens (K n) where
  carrier := { Q : K n | IsUnit ((1 + Q.1 * Q₀.1.transpose).det) }
  is_open' := by
    have hcont : Continuous (fun Q : K n => ((1 + Q.1 * Q₀.1.transpose).det : ℝ)) := by
      fun_prop
    simpa [isUnit_iff_ne_zero] using isOpen_ne_fun hcont continuous_const

/-- The translated Cayley source is nonempty: it contains its center `Q₀`. -/
private lemma cayleySourceAt_nonempty (Q₀ : K n) : Nonempty (cayleySourceAt Q₀) :=
  ⟨⟨Q₀, self_mem_K_open_at Q₀⟩⟩

/-- Repackage the open source subtype of `K n` as the earlier matrix-level
translated Cayley target `K_open_at Q₀`. -/
private noncomputable def cayleySourceEquivAt (Q₀ : K n) :
    cayleySourceAt Q₀ ≃ K_open_at Q₀ where
  toFun Q := ⟨Q.1.1, Q.1.2, Q.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1⟩, Q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- On the open source subtype at `Q₀`, the translated inverse Cayley
formula is continuous. -/
private lemma continuous_cayleyInv_on_sourceAt (Q₀ : K n) :
    Continuous (fun Q : cayleySourceAt Q₀ => cayleyInv (Q.1.1 * Q₀.1.transpose)) := by
  let f : cayleySourceAt Q₀ → K_open n := fun Q =>
    ⟨Q.1.1 * Q₀.1.transpose,
      IsOrthogonal.mul Q.1.2 (IsOrthogonal.transpose Q₀.2),
      Q.2⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    show Continuous (fun Q : cayleySourceAt Q₀ => Q.1.1 * Q₀.1.transpose)
    fun_prop
  simpa [f] using (continuous_cayleyInv_on_KOpen (n := n)).comp hf

/-- On `Sk n`, the translated forward Cayley formula is continuous. -/
private lemma continuous_cayley_mul_on_skew (Q₀ : K n) :
    Continuous (fun X : Sk n => cayley X.1 * Q₀.1) := by
  exact Continuous.matrix_mul continuous_cayley_on_skew continuous_const

/-- The translated Cayley homeomorphism from its natural open source
subtype in `K n` to the model space `Sk n`. -/
private noncomputable def cayleyChartHomeomorphAt (Q₀ : K n) :
    cayleySourceAt Q₀ ≃ₜ Sk n where
  toEquiv := (cayleySourceEquivAt Q₀).trans (cayleyEquivAt Q₀).symm
  continuous_toFun := (continuous_cayleyInv_on_sourceAt (n := n) Q₀).subtype_mk _
  continuous_invFun := by
    simpa [cayleySourceEquivAt, cayleyEquivAt] using
      (((continuous_cayley_mul_on_skew (n := n) Q₀).subtype_mk _).subtype_mk _)

/-- The translated Cayley chart at `Q₀`, bundled as an open partial
homeomorphism on the full orthogonal group `K n`. -/
noncomputable def cayleyOpenChartAt (Q₀ : K n) :
    OpenPartialHomeomorph (K n) (Sk n) :=
  ((cayleySourceAt Q₀).openPartialHomeomorphSubtypeCoe (cayleySourceAt_nonempty Q₀)).symm.trans
    (cayleyChartHomeomorphAt Q₀).toOpenPartialHomeomorph

@[simp] theorem cayleyOpenChartAt_source (Q₀ : K n) :
    (cayleyOpenChartAt Q₀).source =
      { Q : K n | IsUnit ((1 + Q.1 * Q₀.1.transpose).det) } := by
  simp [cayleyOpenChartAt, cayleySourceAt]

@[simp] theorem cayleyOpenChartAt_target (Q₀ : K n) :
    (cayleyOpenChartAt Q₀).target = Set.univ := by
  simp [cayleyOpenChartAt]

/-- The chart centered at `Q` is defined at `Q` itself. -/
theorem self_mem_cayleyOpenChartAt_source (Q : K n) :
    Q ∈ (cayleyOpenChartAt Q).source := by
  simpa [cayleyOpenChartAt_source] using self_mem_K_open_at Q

/-- Full atlas on `K n`, with one translated Cayley chart at each point. -/
noncomputable instance instChartedSpaceK :
    ChartedSpace (Sk n) (K n) where
  atlas := { e | ∃ Q : K n, e = cayleyOpenChartAt Q }
  chartAt Q := cayleyOpenChartAt Q
  mem_chart_source Q := self_mem_cayleyOpenChartAt_source Q
  chart_mem_atlas Q := ⟨Q, rfl⟩

/-! ### IsManifold instance on the full orthogonal group

For the chart compatibility, the transition map in coordinates is
`X ∈ Sk n ↦ cayleyInv (cayley X · Q₀.1 · Q₁.1.transpose)`, on the open
subset where `1 + cayley X · Q₀.1 · Q₁.1.transpose` is invertible.

The proof strategy: factor each `cayleyOpenChartAt Q₀` as
right-translation-by-`Q₀⁻¹` followed by `cayleyOpenChartAt 1`. Since
right-translation is a smooth bijection K → K (preserves the smooth
structure when expressed in chart coordinates as multiplication by a
fixed orthogonal matrix), the chart compatibility for arbitrary Q₀
reduces to the case Q₀ = Q₁ = 1, which is trivial.

The full ContDiffOn proof requires `ContDiff` lemmas for the cayley
formula. The core pieces:

* `ContDiff ℝ ⊤ (cayley : Sk n → Matrix _ _ ℝ)` — cayley is a rational
  function with non-vanishing denominator on Sk (`one_add_skew_isUnit`).
* `ContDiff ℝ ⊤ (· * R)` for fixed orthogonal R — linear map, hence smooth.
* `ContDiffOn ℝ ⊤ cayleyInv {M | (1+M).det.IsUnit}` — rational with
  non-vanishing denominator on its open domain.

Composing gives ContDiffOn for the transition. -/

/-! ### Outline of the remaining `instIsManifoldK` proof

Once we have

* `cayleyChart_transition_contDiffOn (Q₀ Q₁ : K n)` :
  `ContDiffOn ℝ ⊤ (fun X : Sk n => cayleyInv ((cayley X.1 * Q₀.1) * Q₁.1.transpose))`
  on the open set `{X | IsUnit ((1 + (cayley X.1 * Q₀.1) * Q₁.1.transpose).det)}`,

the `IsManifold` instance follows from `isManifold_of_contDiffOn` plus
set-equality bookkeeping that identifies the abstract `(e.symm ≫ₕ e').source`
with the concrete invertibility-of-`1+...` set after unfolding
`cayleyOpenChartAt`.

The transition-smoothness lemma decomposes as

* `cayley` is `ContDiff` (rational with non-vanishing denominator on `Sk n`),
* multiplication by a constant matrix is linear, hence `ContDiff`,
* `cayleyInv` is `ContDiff` on its open domain (rational with non-vanishing
  denominator there).

Each piece uses Mathlib's `ContDiff.bilinear`/`isBoundedBilinearMap_apply.contDiff`
for matrix multiplication and `contDiffAt_ringInverse` (lifted to matrices)
for the inverse, plus `ContDiffOn.comp` and `ContDiffOn.congr` for the
composition. -/

end CayleyTransform

end IwasawaCoC

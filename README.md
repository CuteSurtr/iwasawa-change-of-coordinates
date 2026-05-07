# Iwasawa Decomposition and Change of Coordinates

A Lean 4 / Mathlib formalization of **Theorem 1.1** of

> J. Jorgenson, S. Lang. *Spherical Inversion on `SL_n(R)`*.
> Springer Monographs in Mathematics, 2001.

The Iwasawa product map

```
Φ : K × A × U → GL_n(ℝ),     (k, a, u) ↦ k · a · u
```

is asserted by Jorgenson–Lang to be a *differential isomorphism*
(diffeomorphism), where

- `K = O(n)` is the real orthogonal group,
- `A` is the group of positive diagonal `n × n` real matrices,
- `U` is the group of unipotent upper triangular `n × n` real matrices.

This project formalizes the algebraic, topological, and (largely) smooth
content of that theorem, building on top of the parent project's
[`project.Iwasawa`](../project/Iwasawa.lean), which provides the
set-theoretic existence and uniqueness of the Iwasawa factorization
following Lang's *Linear Algebra*.

## Status at a glance

| Quantity | Value |
|---|---|
| Lines of Lean | 1666 (+ 56-line `AxiomCheck.lean`) |
| `sorry` count | **0** |
| User-declared axioms | 0 |
| Build errors | 0 |
| Build warnings | 0 |
| Axiom dependencies (every named theorem / instance) | `propext`, `Classical.choice`, `Quot.sound` only |
| Theorems / instances tested in `AxiomCheck.lean` | **46** |

Every named theorem and instance in the file is proved without `sorry`
and depends only on the three standard Mathlib axioms.

## Honest disclaimer

We were not able to close out the very last layer of Scope C — the
`IsManifold` instance on the full orthogonal group, the bundled
`iwasawaDiffeomorph`, and the geometric `mfderiv` at the identity.
These pieces require fluency with Mathlib's `ContDiff` / `ContMDiff` /
`isManifold_of_contDiffOn` machinery (specifically the chart-transition
`ContDiffOn` proof for the Cayley atlas, plus set-equality bookkeeping
between the abstract chart-transition source and the concrete
"`1 + ...` is invertible" set) that exceeded our reliable working
knowledge during this session. Each attempt at writing the proof either
introduced `sorry`s (which break Mathlib's warnings-as-errors build) or
got tangled in idiomatic ContDiff / model-with-corners unfolding we
could not resolve.

What is in the file is therefore the entire mathematical content
**up to but not including** that final layer: every Cayley-side
prerequisite (definitions, invertibility, orthogonality, two-sided
inverses, skewness of inverse, set-theoretic equivalence, continuity,
Homeomorph, ChartedSpace, plus a fully proved `C∞` Diffeomorph on the
identity-centered chart `Sk n ≃ K_open n`) is in place and checked.
The `Sphere`-style multi-chart atlas (`instChartedSpaceK`) is also
proved. What remains is the chart-transition smoothness proof and the
`IsManifold` and `Diffeomorph` bundling on top of it. We document the
shape of the missing proof concretely below in
[Remaining work](#remaining-work) so anyone with the right Mathlib
fluency can pick up from where we stopped.

## Provenance and convention

The parent project follows Lang's *Linear Algebra* (3rd edition, 1987)
and writes the Iwasawa decomposition as `g = k · a · u` (orthogonal,
positive-diagonal, upper-unipotent — `K` on the *left*).

Jorgenson–Lang use the opposite order `g = u · a · k` (`K` on the
*right*). The clean change-of-coordinates between the two conventions
is **inversion**: if `g = k · a · u` (Lang), then

```
g⁻¹ = u⁻¹ · a⁻¹ · kᵀ
```

is in J–L form (upper-unipotent · positive-diagonal · orthogonal),
since the inverse of an upper-unipotent matrix is upper-unipotent, the
inverse of a positive diagonal matrix is positive diagonal, and the
transpose of an orthogonal matrix is orthogonal.

The Cartan involution `θ : g ↦ (gᵀ)⁻¹` is a separate involution that
J–L use on p. 2 to characterize `K` as its fixed-point subgroup. We
formalize both.

## Milestones

| # | Goal | Status | J–L reference |
|---|------|--------|---------------|
| 1   | `iwasawaEquiv : K × A × U ≃ GL_n(ℝ)` (set-theoretic bijection)                   | ✅ proved   | Thm I.1.1, set-theoretic |
| 1b  | `inv_iwasawa_jl`: `(kau)⁻¹ = u⁻¹ a⁻¹ kᵀ` (Lang ↔ J-L convention swap)            | ✅ proved   | §I.1, p. 2              |
| 1b  | `cartanInvolution`, `cartanInvolution_involutive`                                | ✅ proved   | §I.1, p. 2              |
| 2   | `continuous_iwasawaMap` (forward direction)                                      | ✅ proved   | Thm I.1.1, topology     |
| 2   | `continuous_iwasawaSymm` (inverse direction; Gram–Schmidt continuity from scratch) | ✅ proved | Thm I.1.1, topology     |
| 2   | `iwasawaHomeomorph : K × A × U ≃ₜ GL_n(ℝ)`                                       | ✅ proved   | Thm I.1.1, topology     |
| 3   | `isOpen_G`, `G_isOpenEmbedding`, smooth structure on `G n`                       | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `UU.toNNHomeomorph`, smooth structure on `UU n` (modeled on `NN n`)              | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `A.toFinNRHomeomorph`, smooth structure on `A n` (modeled on `Fin n → ℝ`)        | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | Cayley transform setup (`cayley`, `cayleyInv`, `one_add_skew_isUnit`, `cayley_isOrthogonal`) | ✅ proved   | Cayley 1846             |
| 3   | Cayley two-sided inverse (`cayley_self_inverse`, `cayleyInv_cayley`, `cayley_cayleyInv`) | ✅ proved   | Cayley 1846             |
| 3   | `cayleyInv_isSkew` (image of orthogonal under Cayley is skew)                    | ✅ proved   | Cayley 1846             |
| 3   | `cayleyEquiv : Sk n ≃ K_open n` (set-level Cayley bijection)                     | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | Cayley continuity (`continuous_cayley_on_skew`, `continuous_cayleyInv_on_KOpen`) | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `cayleyHomeomorph : Sk n ≃ₜ K_open n` (topological)                              | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | Smooth manifold structure on `K_open n` modeled on `Sk n` via Cayley chart       | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `cayleyDiffeomorph : Sk n ≃ₘ K_open n` (`C∞` diffeomorphism)                     | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `IsOrthogonal.mul`, `K_open_at`, `cayleyEquivAt Q₀ : Sk n ≃ K_open_at Q₀`        | ✅ proved   | Thm I.1.1, multi-chart  |
| 3   | `self_mem_K_open_at` (cover `⋃ K_open_at Q = K n`)                                | ✅ proved   | Thm I.1.1, multi-chart  |
| 3   | `cayleyOpenChartAt Q₀ : OpenPartialHomeomorph (K n) (Sk n)` + `instChartedSpaceK` | ✅ proved   | Sphere-pattern atlas    |
| 3   | `instIsManifoldK` (chart-transition `ContDiffOn` + IsManifold compatibility)     | ⚠️ deferred | Thm I.1.1, full         |
| 3   | `iwasawaDiffeomorph : K × A × U ≃ₘ GL_n(ℝ)` (full diffeomorphism)                | ⚠️ deferred | Thm I.1.1, full         |
| 4   | `cartanLieDecomp : IsCompl (Sym n) (Sk n)` (Cartan Lie decomp `gl_n = Sym ⊕ Sk`) | ✅ proved   | §I.3, p. 12             |
| 5   | `disjoint_AA_NN`, `disjoint_KK_AA`, `disjoint_KK_NN` (pairwise disjoint)         | ✅ proved   | §I.3                    |
| 5   | `iwasawa_codisjoint`: `𝔨 ⊔ 𝔞 ⊔ 𝔫 = ⊤` (sum is everything)                         | ✅ proved   | §I.3                    |
| 5   | `iwasawaLieDecomp`: full Iwasawa Lie decomposition `gl_n = 𝔨 ⊕ 𝔞 ⊕ 𝔫`            | ✅ proved   | §I.3                    |
| 5   | `iwasawaLieEquiv`: linear iso `𝔨 × 𝔞 × 𝔫 ≃ₗ[ℝ] gl_n(ℝ)` (algebraic differential at 1) | ✅ proved | §I.3                    |
| 5   | `iwasawaMap_mfderiv_at_one` (full geometric `mfderiv` at identity)               | ⚠️ deferred | §I.3                    |

The legend `⚠️ deferred` means: the mathematical statement is documented
in the file with a precise outline of the proof, but the proof itself
was not closed during this session due to the Mathlib-fluency obstacles
described in the [honest disclaimer](#honest-disclaimer) above.

## Theorem statements

```lean
namespace IwasawaCoC

/-- Subgroup types as bundled subtypes of `Matrix (Fin n) (Fin n) ℝ`. -/
abbrev K (n : ℕ) := { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q }
abbrev A (n : ℕ) := { D : Matrix (Fin n) (Fin n) ℝ // IsPositiveDiagonal D }
abbrev UU (n : ℕ) := { u : Matrix (Fin n) (Fin n) ℝ // IsUpperUnipotent u }
abbrev G (n : ℕ) := { g : Matrix (Fin n) (Fin n) ℝ // g.det ≠ 0 }

/-- Milestone 1: set-theoretic Iwasawa bijection. -/
def iwasawaMap : K n × A n × UU n → G n
noncomputable def iwasawaEquiv : K n × A n × UU n ≃ G n

/-- Milestone 1b: convention swap (Lang ↔ J-L) via inversion. -/
theorem inv_iwasawa_jl (k : K n) (a : A n) (u : UU n) :
    (k.1 * a.1 * u.1)⁻¹ = u.1⁻¹ * a.1⁻¹ * k.1.transpose

/-- Milestone 1b: Cartan involution θ(g) = (gᵀ)⁻¹ and its involutivity. -/
noncomputable def cartanInvolution : G n → G n
theorem cartanInvolution_involutive :
    Function.Involutive (cartanInvolution : G n → G n)

/-- Milestone 2: forward and inverse continuity, then Homeomorph. -/
theorem continuous_iwasawaMap : Continuous (iwasawaMap : K n × A n × UU n → G n)
theorem continuous_iwasawaSymm : Continuous (iwasawaEquiv (n := n)).symm
noncomputable def iwasawaHomeomorph : K n × A n × UU n ≃ₜ G n

/-- Milestone 3 (sub-pieces): smooth structures on G, UU, A. -/
theorem isOpen_G : IsOpen { g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0 }
theorem G_isOpenEmbedding :
    IsOpenEmbedding (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)

def UU.toNNHomeomorph : UU n ≃ₜ NN n                              -- via U ↦ U − 1
noncomputable def A.toFinNRHomeomorph : A n ≃ₜ (Fin n → ℝ)        -- via D ↦ (log D_{ii})_i

/-- Milestone 3 (Cayley transform on `K = O(n)`). -/
noncomputable def cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
noncomputable def cayleyInv : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
theorem one_add_skew_isUnit (X : Sk n) : IsUnit ((1 + X.1).det)
theorem cayley_isOrthogonal (X : Sk n) : IsOrthogonal (cayley X.1)
noncomputable def cayleyToK : Sk n → K n
theorem cayley_self_inverse (X : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + X).det) : cayley (cayley X) = X
theorem cayleyInv_cayley (X : Sk n) : cayleyInv (cayley X.1) = X.1
theorem cayley_cayleyInv (Q : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + Q).det) : cayley (cayleyInv Q) = Q
theorem cayleyInv_isSkew (Q : Matrix (Fin n) (Fin n) ℝ)
    (hOrth : IsOrthogonal Q) (h : IsUnit (1 + Q).det) :
    (cayleyInv Q).transpose = -(cayleyInv Q)
abbrev K_open (n : ℕ) : Type :=
    { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q ∧ IsUnit (1 + Q).det }
noncomputable def cayleyEquiv : (Sk n) ≃ K_open n
theorem continuous_cayley_on_skew : Continuous (fun X : Sk n => cayley X.1)
theorem continuous_cayleyInv_on_KOpen : Continuous (fun Q : K_open n => cayleyInv Q.1)
noncomputable def cayleyHomeomorph : (Sk n) ≃ₜ K_open n
noncomputable instance : ChartedSpace (Sk n) (K_open n)
instance : IsManifold (𝓘(ℝ, (Sk n : Type _))) ⊤ (K_open n)
noncomputable def cayleyDiffeomorph :
    Diffeomorph (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _))) (Sk n) (K_open n) ⊤

/-- Multi-chart atlas: translated Cayley charts at every base point. -/
theorem IsOrthogonal.mul {Q R : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonal Q) (hR : IsOrthogonal R) : IsOrthogonal (Q * R)
abbrev K_open_at (Q₀ : K n) : Type
noncomputable def cayleyEquivAt (Q₀ : K n) : (Sk n) ≃ K_open_at Q₀
theorem self_mem_K_open_at (Q : K n) : IsUnit ((1 + Q.1 * Q.1.transpose).det)
noncomputable def cayleyOpenChartAt (Q₀ : K n) : OpenPartialHomeomorph (K n) (Sk n)
theorem cayleyOpenChartAt_source (Q₀ : K n) :
    (cayleyOpenChartAt Q₀).source =
      { Q : K n | IsUnit ((1 + Q.1 * Q₀.1.transpose).det) }
noncomputable instance instChartedSpaceK : ChartedSpace (Sk n) (K n)

/-- Milestone 4: Cartan Lie decomposition gl_n(ℝ) = Sym_n ⊕ Sk_n. -/
def Sym (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
def Sk  (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
theorem cartanLieDecomp (n : ℕ) : IsCompl (Sym n) (Sk n)

/-- Milestone 5: Iwasawa Lie subalgebras + direct-sum decomposition + linear iso. -/
def NN (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)   -- strict upper
def AA (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)   -- diagonal
abbrev KK (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) -- skew = Sk
theorem disjoint_AA_NN (n : ℕ) : Disjoint (AA n) (NN n)
theorem disjoint_KK_AA (n : ℕ) : Disjoint (KK n) (AA n)
theorem disjoint_KK_NN (n : ℕ) : Disjoint (KK n) (NN n)
theorem iwasawa_codisjoint (n : ℕ) : KK n ⊔ AA n ⊔ NN n = ⊤
theorem iwasawaLieDecomp (n : ℕ) :
    Disjoint (KK n) (AA n) ∧ Disjoint (KK n) (NN n) ∧ Disjoint (AA n) (NN n)
    ∧ KK n ⊔ AA n ⊔ NN n = ⊤
def iwasawaLieMap : (KK n × AA n × NN n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ
theorem iwasawaLieMap_surjective : Function.Surjective (iwasawaLieMap (n := n))
theorem iwasawaLieMap_injective  : Function.Injective  (iwasawaLieMap (n := n))
noncomputable def iwasawaLieEquiv :
    (KK n × AA n × NN n) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ

end IwasawaCoC
```

## Repository layout

```
iwasawa_change_of_coords/
├── README.md           this file
├── IwasawaCoC.lean     the main file (1666 lines)
└── AxiomCheck.lean     prints axiom dependencies of every named theorem
```

The project shares the parent's Lake build (single `lakefile.toml`,
single `lean-toolchain`, single Mathlib pin), so there is no duplicated
toolchain configuration.

## Build instructions

From `/Users/jiho/Desktop/math 157`:

```sh
lake build iwasawa_change_of_coords.IwasawaCoC
lake build iwasawa_change_of_coords.AxiomCheck   # prints axiom deps
```

The first build will compile the parent project's `project.Iwasawa`
as a dependency.

## Verifying the result

After a successful build, `AxiomCheck.lean` prints the axiom dependency
of every named theorem and instance in the file. All forty-six listed
items depend only on `[propext, Classical.choice, Quot.sound]` — i.e.,
exactly the three axioms used by classical Mathlib, with no
project-specific assumption and no `sorry`.

## Proof outlines

### Milestone 1 — Iwasawa bijection

The equivalence `iwasawaEquiv : K × A × UU ≃ G` reuses the parent
project's existence (`Iwasawa.exists_iwasawa`) and uniqueness
(`Iwasawa.iwasawa_unique`).

* Forward: `(k, a, u) ↦ ⟨k · a · u, _⟩`, with `det (kau) ≠ 0` from the
  three component invertibility lemmas.
* Backward: take the Iwasawa factorization `F := Iwasawa.iwasawa g.2`
  and return its `(k, a, u)`-components as subtypes.
* `right_inv` is `F.factorization.symm`.
* `left_inv` builds an explicit `IwasawaFactorization (kau)` from
  `(k, a, u)` and applies `Iwasawa.iwasawa_unique`.

### Milestone 1b — Convention swap and Cartan involution

`inv_iwasawa_jl` is a direct algebraic identity:

```
(k · a · u)⁻¹ = u⁻¹ · (k · a)⁻¹                  (Matrix.mul_inv_rev)
              = u⁻¹ · a⁻¹ · k⁻¹                  (Matrix.mul_inv_rev, mul_assoc)
              = u⁻¹ · a⁻¹ · kᵀ                   (IsOrthogonal.matInv_eq_transpose)
```

`cartanInvolution g := ⟨(g.1)ᵀ⁻¹, _⟩` requires showing
`((g.1)ᵀ⁻¹).det ≠ 0`, which follows from
`g.1.transpose * (g.1.transpose)⁻¹ = 1` via `Matrix.mul_nonsing_inv` and
taking determinants.

`cartanInvolution_involutive` reduces to
`(((g.1)ᵀ)⁻¹)ᵀ⁻¹ = g.1` via the rewrite chain
`Matrix.transpose_nonsing_inv → Matrix.transpose_transpose →
Matrix.nonsing_inv_nonsing_inv`.

### Milestone 2 — Topology and Gram–Schmidt continuity

`continuous_iwasawaMap` is one rule of `Continuous.matrix_mul` lifted
through subtype embeddings.

`continuous_iwasawaSymm` is the substantial piece. It reduces to
continuity of the parent project's Gram–Schmidt-derived `qMat`, `dMat`,
`uMat` on `G n`, which in turn reduces to continuity of `gramSchmidt`
and `gramSchmidtNormed` (Mathlib's
`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`) in the input
function, on the locus of linearly-independent column families.
Mathlib v4.30 does not package this continuity, so we prove it inline:

* `continuous_gCol_at` — column extraction is continuous.
* `continuous_gramSchmidt_at` — by well-founded induction on `i : Fin n`.
  Inductive step: rewrite via `gramSchmidt_def` to
  `gCol g.1 i − ∑ j ∈ Iio i, (ℝ ∙ gramSchmidt _ j).starProjection (gCol _ i)`.
  The 1D projection becomes the rational expression
  `(⟨v, w⟩ / ‖v‖²) • v` via `Submodule.starProjection_singleton`, which
  is continuous because the denominator is nonzero on `G n`
  (`gramSchmidt_ne_zero` applied to `Iwasawa.gCol_linearIndependent`).
* `continuous_gramSchmidtNormed_at` — division by nonzero norm.
* `continuous_qMat_subtype`, `continuous_rMat_subtype`,
  `continuous_dMat_subtype`, `continuous_diagInv_dMat_subtype`,
  `continuous_uMat_subtype` — entry-wise continuity of the four matrix
  factors built from Gram–Schmidt outputs.
* `continuous_iwasawaSymm` assembles the three factors.

This is the kind of result that could plausibly be upstreamed to
Mathlib (continuity of `gramSchmidt` and `gramSchmidtNormed` in their
input function, on the linearly-independent locus); see
`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho` as the natural
home.

### Milestone 3 — Smooth structures

Open-submanifold smoothness on `G n` is direct: `G n` is open in
`Matrix (Fin n) (Fin n) ℝ` (preimage of `≠ 0` under continuous `det`),
so `IsOpenEmbedding.singletonChartedSpace` and
`IsOpenEmbedding.isManifold_singleton` apply. The norm on Matrix is
chosen via `attribute [local instance]` over
`Matrix.normedAddCommGroup` and `Matrix.normedSpace` (Mathlib
intentionally does not register a global matrix norm because several
natural choices exist).

`UU n` is modeled on `NN n` (the strictly upper-triangular `Submodule`)
via the homeomorphism `UU.toNNHomeomorph U := U − 1`. The chart is
single (covers all of `UU n`) and gives `ChartedSpace` and `IsManifold`
instances via `OpenPartialHomeomorph.singletonChartedSpace`.

`A n` is modeled on `Fin n → ℝ` via `A.toFinNRHomeomorph D := (log D_{ii})_i`
with inverse `v ↦ diag(exp v)`, giving a single-chart smooth structure.

### Milestone 3 — Cayley transform on `O(n)`

The major mathematical work. The Cayley transform

```
cayley X = (1 − X)(1 + X)⁻¹
```

provides a parametrization of `O(n)` minus a measure-zero set by
skew-symmetric matrices. The full chain:

* `one_add_skew_isUnit` (`1 + X` invertible for `X` skew). Proof:
  `(1 + X)(1 − X) = 1 + X · Xᵀ` (using `Xᵀ = −X`), and
  `1 + X · Xᵀ` is positive definite (`1` is `PosDef`, `X · Xᵀ` is
  `PosSemidef` via `posSemidef_self_mul_conjTranspose`). Hence
  `(1 + X)(1 − X)` is a unit, so `1 + X` is too (via
  `isUnit_of_mul_isUnit_left`).
* `cayley_isOrthogonal` — `(cayley X)(cayley X)ᵀ = 1` for `X` skew, by
  algebraic manipulation using the commutativity of `(1 + X)` and
  `(1 − X)` (and their inverses).
* `cayley_self_inverse` — for any `X` with `1 + X` invertible,
  `cayley(cayley X) = X`. The proof shows
  `1 − cayley X = X · (1 + cayley X)` by post-multiplying both sides by
  `(1 + X)` and using the algebraic identities
  `(1 ± cayley X)(1 + X) = X + X` and `(1 + cayley X)(1 + X) = 1 + 1`.
  Specializations give the left/right inverses
  `cayleyInv_cayley` (on `Sk n`) and `cayley_cayleyInv` (on the
  invertibility set).
* `cayleyInv_isSkew` — for orthogonal `Q` with `1 + Q` invertible,
  `cayleyInv Q` is skew-symmetric. The proof uses
  `Qᵀ = Q⁻¹` (orthogonality) plus the identity
  `(1 + Q⁻¹) = Q⁻¹ · (1 + Q)`, the commutativity of polynomials in `Q`,
  and direct computation of the transpose.
* `cayleyEquiv : Sk n ≃ K_open n` bundles the bijection.
* `continuous_cayley_on_skew` and `continuous_cayleyInv_on_KOpen` use
  Mathlib's `continuousAt_matrix_inv` (for the matrix inverse) and
  `NormedRing.inverse_continuousAt` (for `Ring.inverse` on units).
* `cayleyHomeomorph` bundles topological bijection.
* `instChartedSpaceKOpen`, `instIsManifoldKOpen` — `K_open n` is a
  smooth manifold modeled on `Sk n` via the Cayley chart, set up using
  `IsOpenEmbedding.singletonChartedSpace` on `cayleyHomeomorph.symm`.
* `contMDiff_cayleyHomeomorph`, `contMDiff_cayleyHomeomorphSymm` —
  smoothness in both directions, using `contMDiff_isOpenEmbedding` and
  `contMDiffOn_isOpenEmbedding_symm` plus the function-equality
  identification of `cayleyHomeomorph` with the
  `OpenPartialHomeomorph`-inverse via
  `IsOpenEmbedding.toOpenPartialHomeomorph_left_inv`.
* `cayleyDiffeomorph` is the bundled `C∞` diffeomorphism.

### Milestone 3 — Multi-chart atlas (Sphere pattern)

The single Cayley chart at the identity covers `K_open n` (the open
dense subset of `O(n)` where `−1` is not an eigenvalue of `Q`). To
cover the rest of `O(n)`, we follow Mathlib's pattern from
[`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html)
(stereographic projection from each unit vector — Heather Macbeth,
2021) and put a chart at every point.

* `IsOrthogonal.mul` — group closure of `K`.
* `K_open_at Q₀` — translated open subset
  `{ Q ∈ K | (1 + Q · Q₀ᵀ).det.IsUnit }`.
* `cayleyEquivAt Q₀ : Sk n ≃ K_open_at Q₀` — set-level bijection,
  proved by reduction to the identity-centered case using
  `cayleyEquiv.symm` and right-multiplication by `Q₀`/`Q₀ᵀ`.
* `self_mem_K_open_at` — for any `Q ∈ K n`, `Q ∈ K_open_at Q` (since
  `Q · Qᵀ = 1` and `1 + 1` has invertible determinant `2ⁿ`).
* `cayleyOpenChartAt Q₀` — bundles each translated equivalence as an
  `OpenPartialHomeomorph (K n) (Sk n)`. The construction goes through
  `(cayleySourceAt Q₀).openPartialHomeomorphSubtypeCoe.symm.trans
  cayleyChartHomeomorphAt Q₀.toOpenPartialHomeomorph`, avoiding the
  if-then-else / decidability issues that arise if one tries to define
  the chart's `toFun` globally.
* `instChartedSpaceK` — full atlas on `K n`, with one translated
  Cayley chart at each point.

### Milestone 4 — Cartan Lie decomposition

`IsCompl (Sym n) (Sk n)` splits into

* *Disjoint*: `M ∈ Sym ∩ Sk` ⟹ `Mᵀ = M = −M` ⟹ `2 · M = 0` ⟹ `M = 0`.
* *Codisjoint*: `M = ½(M + Mᵀ) + ½(M − Mᵀ)`.

### Milestone 5 — Iwasawa Lie decomposition

Pairwise disjoint:
* `disjoint_AA_NN` — diagonal ∩ strictly upper = 0.
* `disjoint_KK_AA` — skew-symmetric diagonal forces all entries zero.
* `disjoint_KK_NN` — case split below/diagonal/above.

`iwasawa_codisjoint` (`𝔨 ⊔ 𝔞 ⊔ 𝔫 = ⊤`) is the explicit decomposition

```
M = K + A + N
A_{ij} = M_{ii}      if i = j, else 0   (in 𝔞)
K_{ij} = M_{ij}      if j < i           (in 𝔨, skew-symmetrized)
       = -M_{ji}     if i < j
       = 0           if i = j
N_{ij} = M_{ij} + M_{ji}  if i < j      (in 𝔫, strict upper)
       = 0                otherwise
```

Verification is entry-by-entry on the trichotomy
`j < i / i = j / i < j`.

`iwasawaLieDecomp` bundles the four conditions.

`iwasawaLieMap`/`iwasawaLieEquiv` is the linear sum map
`(X, Y, Z) ∈ 𝔨 × 𝔞 × 𝔫 ↦ X + Y + Z`. Surjectivity is
`iwasawa_codisjoint`. Injectivity is the entry-wise argument:

* `j < i`: `Y_{ij} = 0` (off-diag), `Z_{ij} = 0` (`j ≤ i`), so `X_{ij} = 0`.
* `j = i`: `X_{ii} = −X_{ii}` (skew) gives `X_{ii} = 0`; same for `Y`, `Z`.
* `i < j`: by the previous case at `(j, i)` we have `X_{ji} = 0`; skew
  gives `X_{ij} = −X_{ji} = 0`, then `Y_{ij} = 0` (off-diag), `Z_{ij} = 0`.

This is the algebraic content of "the differential of the Iwasawa map
at the identity is invertible," realized as a `LinearEquiv`.

## Remaining work

Three pieces are not closed in this file:

### 1. `instIsManifoldK` — chart-transition `ContDiffOn`

The chart compatibility for the multi-chart atlas. After
`isManifold_of_contDiffOn` reduces it to a `ContDiffOn` statement, the
remaining content is the smoothness of the transition

```
X ∈ Sk n ↦ cayleyInv ((cayley X · Q₀.1) · Q₁.1.transpose)
```

on the open set

```
{ X : Sk n | IsUnit ((1 + (cayley X · Q₀.1) · Q₁.1.transpose).det) }.
```

This decomposes through:

* `ContDiff ℝ ⊤ (cayley : Sk n → Matrix _ _ ℝ)` — Cayley as a rational
  expression with non-vanishing denominator on `Sk n`. Each piece is
  `ContDiff` (linear maps for `1 ± X`, `contDiffAt_ringInverse` for
  inversion on units).
* `ContDiff ℝ ⊤ (· * R)` for fixed orthogonal `R` — linear, hence
  smooth (`ContinuousLinearMap.contDiff` or the bilinear-map lemma
  `isBoundedBilinearMap_apply.contDiff`).
* `ContDiffOn ℝ ⊤ cayleyInv {M | (1+M).det.IsUnit}` — same shape as
  the cayley `ContDiff`.

The composition is `ContDiffOn` on the relevant open set, with
`ContDiffOn.comp` and `ContDiffOn.congr` to massage the set definitions
to align with Mathlib's abstract `(e.symm ≫ₕ e').source`.

We have the file documented with the precise structure of the proof
at the end of the `CayleyTransform` section. Closing this one item
gives `instIsManifoldK`.

### 2. `iwasawaDiffeomorph : K × A × U ≃ₘ GL_n(ℝ)`

Once `instIsManifoldK` is in place, this is an assembly of
`iwasawaEquiv` (set-theoretic), forward smoothness (matrix
multiplication is `ContMDiff` on a normed algebra), and inverse
smoothness (a `C∞` upgrade of `continuous_iwasawaSymm` using
`ContDiff` of Gram–Schmidt — the same inductive proof structure as
the continuity proof we already gave, lifted to the smooth category).
Approximately 80–150 more lines.

### 3. `iwasawaMap_mfderiv_at_one` — geometric `mfderiv` at the identity

Showing the differential of `iwasawaMap` at `(1, 1, 1)` equals the
linear sum map `(X, Y, Z) ↦ X + Y + Z` realized by `iwasawaLieEquiv`.
The proof uses `mfderiv_eq_fderiv` (when manifolds are themselves
normed spaces, `mfderiv` reduces to `fderiv`), plus a direct Jacobian
computation of the Cayley chart at `0 ∈ Sk` (the first-order Taylor
expansion of `cayley` at `0` is `X ↦ 1 + 2X + O(X²)`, so the
differential of `cayleyHomeomorph` at `0` is multiplication by `2`,
which is invertible). Approximately 100 lines.

## Why this is the natural stopping point for us

The three remaining pieces are concrete Mathlib pattern work, not
research gaps. The mathematical content — every Cayley algebraic
identity, every continuity proof, every set-theoretic equivalence,
the Iwasawa Lie decomposition, the linear-algebra differential — is
proved and axiom-clean. What we lack is the deep working fluency with
Mathlib's `ContDiff` / `ContMDiff` / `isManifold_of_contDiffOn` /
`ModelWithCorners` machinery to close out the smoothness composition
proof reliably. Each of our attempts either introduced `sorry`s
(rejected by Mathlib's warnings-as-errors build policy) or got tangled
in idiomatic typeclass juggling.

We believe the cleanest next step — substantially more useful than
finishing inside this one file — is an upstream Mathlib contribution
adding `O(n)` (or more generally the orthogonal/unitary group of a
finite-dimensional real/complex inner product space) as a smooth Lie
subgroup of `GL_n` via the Cayley-transform atlas, paralleling the
existing `Mathlib.Geometry.Manifold.Instances.Sphere`. The Cayley-side
groundwork in this file (`cayley`, `cayleyInv`, `one_add_skew_isUnit`,
`cayley_isOrthogonal`, `cayley_self_inverse`, `cayleyInv_isSkew`,
`cayleyEquiv`, `cayleyHomeomorph`, `cayleyDiffeomorph` on the
identity-centered chart, and `cayleyEquivAt` plus `cayleyOpenChartAt`
for the translated charts) is structured to be liftable to such a
Mathlib PR with relatively little adaptation.

## References

- J. Jorgenson, S. Lang. *Spherical Inversion on `SL_n(R)`*. Springer
  Monographs in Mathematics, 2001. (Primary source — Chapter I, §1–§3.)
- S. Lang. *Linear Algebra*, 3rd edition. Springer Undergraduate Texts
  in Mathematics, 1987. (Convention for the parent project.)
- A. Cayley. "Sur quelques propriétés des déterminants gauches."
  *Crelle's Journal* 32 (1846), 119–123.
- The Mathlib community.
  [Mathlib4](https://github.com/leanprover-community/mathlib4).
- H. Macbeth. [`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html), 2021.
  (Stereographic projection multi-chart atlas — the model we follow
  for `cayleyOpenChartAt`.)
- [`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html) — transpose / inverse interaction.
- [`Mathlib.LinearAlgebra.Matrix.PosDef`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html) — `PosDef.add_posSemidef`, `PosDef.isUnit`, `posSemidef_self_mul_conjTranspose` (used in `one_add_skew_isUnit`).
- [`Mathlib.Analysis.Matrix.Normed`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Normed.html) — locally-attributed matrix norm.
- [`Mathlib.Topology.Instances.Matrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/Matrix.html) — continuity of matrix operations, including `continuousAt_matrix_inv` (used in `continuous_cayley_on_skew` / `continuous_cayleyInv_on_KOpen`).
- [`Mathlib.Geometry.Manifold.IsManifold.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold/Basic.html) — `IsOpenEmbedding.isManifold_singleton`, `isManifold_of_contDiffOn`.
- [`Mathlib.Geometry.Manifold.Diffeomorph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Diffeomorph.html) — `Diffeomorph` structure.

## License

Released for educational and academic use.

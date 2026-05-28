# Mathlib Infrastructure Map for the Iwasawa Decomposition Project

Phase 1 notes, written 2026-05-22, from a survey of Mathlib's manifold,
Lie algebra, and measure theory modules, plus searches of arXiv, Lean
Zulip, and Mathlib4 GitHub. This document
consolidates the findings into a decision-grade map of what Mathlib
provides versus what the Iwasawa project must build from scratch.

## Top-line conclusions

1. **GL_n manifold structure is plug-and-play.**
   `Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra` provides
   `ChartedSpace`, `IsManifold`, and `LieGroup 𝓘(𝕜, R) n Rˣ` for any
   complete normed ring `R`. For `R = Matrix (Fin n) (Fin n) ℝ`, this
   gives the full Lie group structure on `(Matrix _ _ ℝ)ˣ`. Our
   project's `G n = {M : Matrix _ _ ℝ | M.det ≠ 0}` subtype is
   essentially the same as `Units`, modulo a `MulEquiv` (det ≠ 0 ↔
   invertible). All open-submanifold instances transfer.

2. **No Lie group `Ad` and no `exp`.** Both are absent from Mathlib's
   manifold infrastructure. PR #37932 (open, idontgetoutmuch,
   2026-04-11) is in progress for the exponential map's smoothness but
   not yet merged. The Iwasawa project must define both ad hoc.

3. **Cartan involution / Cartan decomposition: nothing.** Mathlib has
   `IsKilling` (Killing form non-singularity), `IsCartanSubalgebra`
   (nilpotent + self-normalizing), the full root-system/Geck
   apparatus, and Engel's theorem, but **zero infrastructure** for:
   - Cartan involution `θ : g → g` of order 2 with positive-definite
     `−κ(X, θY)`.
   - Cartan decomposition `g = k ⊕ p` into ±1 eigenspaces.
   - Restricted root system on a real maximal abelian `a ⊂ p`.
   - Iwasawa decomposition `g = k ⊕ a ⊕ n`.
   - Real-form-specific Killing form signature.

   The Tier 2 / Tier 3 layers of this project are genuinely new code.

4. **Haar measure infrastructure is solid for the abstract setup.**
   `Measure.haarMeasure`, `IsHaarMeasure`, `Measure.modularCharacter`,
   `Measure.haarScalarFactor`, `Measure.distribHaarChar`,
   `mulEquivHaarChar`, plus `MeasureTheory/Function/Jacobian.lean`'s
   change-of-variables theorems (`integral_image_eq_integral_abs_det_fderiv_smul`
   in particular) cover the abstract framework. The Iwasawa-specific
   formulas (`δ(diag a) = ∏_{i<j} aᵢ/aⱼ`, `det(d iwasawaMap)`,
   pushforward identity) are new theorems but their general
   machinery is in place.

5. **Active Mathlib development in adjacent areas.** Oliver Nash has
   been landing root system / Cartan matrix / Killing form PRs at a
   steady cadence through 2025-2026 (Geck construction, base of root
   system, semisimplicity criteria via Killing). jano-wol contributed
   the Killing-orthogonal complement and Cartan's criterion. None of
   this work touches real Lie groups or Iwasawa.

---

## Deliverable 1a: Manifold and Lie group infrastructure

### Files read (10)

`Mathlib/Geometry/Manifold/Algebra/{LieGroup, LeftInvariantDerivation, Monoid, SmoothFunctions}.lean`,
`Mathlib/Geometry/Manifold/MFDeriv/{Basic, Atlas, SpecificFunctions}.lean`,
`Mathlib/Geometry/Manifold/Diffeomorph.lean`,
`Mathlib/Geometry/Manifold/Instances/{UnitsOfNormedAlgebra, Sphere}.lean`.

### Coverage by category

**Left/right translation smoothness (Monoid.lean):**
`contMDiff_mul_left`, `contMDiffAt_mul_left`, `contMDiff_mul_right`,
`contMDiffAt_mul_right`, `mdifferentiable_mul_left`,
`mdifferentiableAt_mul_left`, `smoothLeftMul I g : C^∞⟮I, G; I, G⟯`
(notation `𝑳 I g`), `smoothRightMul I g` (notation `𝑹 I g`).
**Direct match for the smoothness component of `mfderiv_leftMul_at`.**

**Left/right translation derivative (closed form):** Not directly
available. Must descend through `extChartAt`/`chartAt` for the target
manifold. For `Units`-style charted spaces (like `G n`), the chart is
identity, so the descent reduces to fderiv on the ambient algebra.

**Inversion smoothness (LieGroup.lean):**
`contMDiff_inv`, `ContMDiff.inv`, `ContMDiffAt.inv`, `ContMDiff.div`,
`Prod.instLieGroup`.

**Lie group instance for units (UnitsOfNormedAlgebra.lean):**
- `Units.instance : ChartedSpace R Rˣ` (via `singletonChartedSpace`)
- `Units.instance : IsManifold 𝓘(𝕜, R) n Rˣ`
- `Units.contMDiff_val`
- `Units.instance : LieGroup 𝓘(𝕜, R) n Rˣ`

**DIRECT MATCH** if we route through `(Matrix _ _ ℝ)ˣ`.

**Chain rule and core mfderiv API (MFDeriv/Basic.lean):**
`mfderiv_comp x hg hf`, `HasMFDerivAt.comp`,
`MDifferentiableAt.hasMFDerivAt`, `HasMFDerivAt.mfderiv`,
`ContMDiffAt.mdifferentiableAt`, `Filter.EventuallyEq.mfderiv_eq`.

**Chart-level differentials (MFDeriv/Atlas.lean):**
`mdifferentiable_chart`, `OpenPartialHomeomorph.MDifferentiable.mfderiv`
(returning a `≃L[𝕜]`), `mfderiv_extChartAt_self`,
`isInvertible_mfderiv_extChartAt`.

**Specific function differentials (MFDeriv/SpecificFunctions.lean):**
- Identity/const/CLM/CLE → `hasMFDerivAt_id`, `mfderiv_const`,
  `ContinuousLinearMap.hasMFDerivAt`, etc.
- Product → `HasMFDerivAt.prodMk`, `mfderiv_prodMk` (DIRECT MATCH),
  `hasMFDerivAt_fst`/`_snd`.
- Arithmetic → `HasMFDerivAt.add`, `.sub`, `.neg`, `.const_smul`,
  `mfderiv_add`, etc.
- **`HasMFDerivAt.mul'`** for `NormedRing` codomain (DIRECT MATCH for
  conjugation derivative).

**Lie algebra realization (LeftInvariantDerivation.lean):**
`LeftInvariantDerivation I G` carries `LieRing` + `LieAlgebra` via
commutator. Uses `𝒅ₕ (smoothLeftMul_one I g)` for the invariance
axiom. No `Ad` is defined; no `exp`.

### Direct-match summary for Phase 2 targets

| Target | Direct match? | Building blocks |
|--------|---------------|-----------------|
| `mfderiv_leftMul_at` (T1-4 L1) | Partial (smoothness only) | `contMDiff_mul_left`, `mdifferentiableAt_mul_left`, descend via `Units.val` chart |
| `conjugation_NN_by_diagonal` (T1-4 L2) | No | `HasMFDerivAt.mul'` × 2, `ContMDiff.inv`, `mfderiv_const` |
| Gram-Schmidt smoothness (T1-2) | No | Prove `ContDiffOn` on invertibles, transfer via `ContMDiff.of_comp_isOpenEmbedding` |

---

## Deliverable 1b: Lie algebra and Killing form infrastructure

### Files read (8)

`Mathlib/Algebra/Lie/{Basic, Killing, Engel, CartanSubalgebra}.lean`,
`Mathlib/Algebra/Lie/Semisimple/Basic.lean`,
`Mathlib/Algebra/Lie/Weights/{Basic, Killing}.lean`,
`Mathlib/Algebra/Lie/Derivation/Killing.lean`. Plus auxiliary:
`OfAssociative.lean`, `AdjointAction/{Basic, Derivation}.lean`,
`Matrix.lean`, `SkewAdjoint.lean`, `Classical.lean`, `TraceForm.lean`.

### Coverage by category

**`ad` and `Ad` infrastructure (OfAssociative.lean +
AdjointAction/Basic.lean):**
- `LieModule.toEnd R L M : L →ₗ⁅R⁆ Module.End R M`
- `LieAlgebra.ad R L := LieModule.toEnd R L L`
- `ad_apply : ad R L x y = ⁅x, y⁆`
- `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`: for associative `A`,
  `ad a = L_a − R_a`. **DIRECT MATCH** for matrix-level `ad`.
- `ad_nilpotent_of_nilpotent`, `ad_isSemisimple_of_isSemisimple`,
  `commute_ad_of_commute`.

No `LieGroup.Ad` (Lie-group-level conjugation differential).

**Killing form (Killing.lean + TraceForm.lean + Weights/Killing.lean):**
- `killingForm R L := LieModule.traceForm R L L`
- `killingForm_apply_apply : κ x y = tr(ad x ∘ ad y)`
- `LieAlgebra.IsKilling` class (Killing form non-singular)
- `LieAlgebra.restrict_killingForm` (restriction to subalgebra)
- `IsKilling.killingForm_nondegenerate`, `IsKilling.instSemisimple`
- `killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero` (root
  spaces are Killing-orthogonal unless α + β = 0)
- `restrict_killingForm_eq_sum`: `κ|H = Σ_α α ⊗ α`
- `cartanEquivDual`, `coroot`, `root_apply_coroot = 2`

**No real-form signature lemmas.** `κ < 0 on k`, `κ > 0 on p` is not
proved anywhere. The standard `κ_{sl_n}(X,Y) = 2n · tr(XY)` is absent.

**Cartan subalgebra (CartanSubalgebra.lean):**
- `LieSubalgebra.IsCartanSubalgebra` (nilpotent + self-normalizing)
- `isCartanSubalgebra_iff_isUcsLimit`
- `LieAlgebra.top_isCartanSubalgebra_of_nilpotent`

**Construction of Cartan subalgebras** lives in `CartanExists.lean`
(not read in detail).

**Engel's theorem (Engel.lean):** `LieAlgebra.isEngelian_of_isNoetherian`,
`LieAlgebra.isNilpotent_iff_forall`. Used for nilpotency arguments,
including the lower central series of `n`.

**Semisimple structure (Semisimple/Basic.lean):**
`HasTrivialRadical`, `IsSemisimple`, `IsSimple`, ideal lattice as
boolean algebra, `ad_ker_eq_bot_of_hasTrivialRadical`.

**Weight/root theory (Weights/Basic.lean + Weights/Killing.lean):**
- `LieModule.weightSpace`, `genWeightSpace`, `posFittingComp`
- `IsTriangularizable` class, `iSup_genWeightSpace_eq_top`
- `IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra` (over perfect
  field, ad h is semisimple for h ∈ Cartan)
- `IsKilling.instIsLieAbelianOfIsCartanSubalgebra`
- `exists_isSl2Triple_of_weight_isNonZero`, `IsSl2Triple.h_eq_coroot`
- `finrank_rootSpace_eq_one`, `sl2SubalgebraOfRoot`
- `Weight.instInvolutiveNeg` (root negation)
- `span_weight_eq_top`, `iInf_ker_weight_eq_bot`

**No restricted root system** for real semisimple Lie algebras with a
chosen Cartan involution.

**Matrix / classical interface:**
- `Matrix.lieEquivMatrix' : End R (n → R) ≃ₗ⁅R⁆ Matrix n n R`
- `Matrix.lie_apply : ⁅A, v⁆ = A *ᵥ v`
- `Matrix.lieConj P h` (conjugation by invertible)
- `LieAlgebra.SpecialLinear.sl n R`, `Orthogonal.so`, `Orthogonal.so'`,
  `Symplectic.sp`
- `skewAdjointLieSubalgebra`, `skewAdjointMatricesLieSubalgebra`,
  `Matrix.lie_transpose`
- `LieAlgebra.ofAssociativeAlgebra` instance: `Matrix n n R` is
  automatically a `LieAlgebra R`.

### Gaps (Tier 2-relevant)

| Gap | Severity |
|-----|----------|
| No `CartanInvolution` class | Total — must write from scratch |
| No `g = k ⊕ p` decomposition | Total |
| No restricted root system | Total |
| No real Killing signature | Total |
| `Ad` (Lie group level) | Total |
| Exponential map (`exp`) | In progress (PR #37932) |
| No `gl_n(ℝ)`-specific Killing formula | Total |

The Tier 2 layer of this project will need to introduce `CartanInvolution`,
`CartanDecomposition`, and prove the standard real-Killing signature
lemmas for `gl_n(ℝ)`. The eligible existing primitives are:
`Orthogonal.so` (gives `k`), `LieAlgebra.SpecialLinear.sl` (gives the
traceless part of `gl`), `restrict_killingForm_eq_sum` (basis for
restricted root theory), `IsSl2Triple` (for restricted root sl₂'s).

---

## Deliverable 1c: Measure theory and Haar infrastructure

### Files read (7)

`Mathlib/MeasureTheory/Measure/Haar/{Basic, OfBasis, Unique, MulEquivHaarChar}.lean`,
`Mathlib/MeasureTheory/Group/{ModularCharacter, Measure}.lean`,
`Mathlib/MeasureTheory/Function/Jacobian.lean`. Plus
`Haar/DistribChar.lean` (auxiliary).

### Coverage by category

**Haar existence (Haar/Basic.lean):**
`Measure.haarMeasure`, `Measure.haar`, `haarMeasure_self`,
`isMulLeftInvariant_haarMeasure`, `regular_haarMeasure`,
`sigmaFinite_haarMeasure`, `isHaarMeasure_haarMeasure`,
`haarMeasure_unique`, `regular_of_isMulLeftInvariant`,
`div_mem_nhds_one_of_haar_pos` (Steinhaus).

**Basis-induced Haar on finite-dim vector spaces (Haar/OfBasis.lean):**
`Module.Basis.addHaar`, `parallelepiped`, `Basis.addHaar_eq_iff`,
`Basis.prod_addHaar`, `Basis.addHaar_reindex`,
`measureSpaceOfInnerProductSpace`.

**Haar uniqueness (Haar/Unique.lean):**
`Measure.haarScalarFactor μ' μ : ℝ≥0`,
`integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`,
`haarScalarFactor_self`, `haarScalarFactor_eq_mul`,
`measure_isMulInvariant_eq_smul_of_isCompact_closure`,
`measure_isHaarMeasure_eq_smul_of_isOpen`,
`isMulLeftInvariant_eq_smul_of_regular`,
`isMulLeftInvariant_eq_smul`, `isMulInvariant_eq_smul_of_compactSpace`,
`isHaarMeasure_eq_of_isProbabilityMeasure`,
`MonoidHom.measurePreserving`, `haarScalarFactor_map`.

**Pushforward up to scalar (Haar/MulEquivHaarChar.lean):**
`mulEquivHaarChar φ : ℝ≥0 := haarScalarFactor haar (haar.map φ)`,
`mulEquivHaarChar_smul_map`, `mulEquivHaarChar_pos`,
`mulEquivHaarChar_eq`, `mulEquivHaarChar_smul_integral_map`,
`integral_comap_eq_mulEquivHaarChar_smul`,
`mulEquivHaarChar_smul_preimage`, `mulEquivHaarChar_refl`,
`mulEquivHaarChar_trans` (group hom), `mulEquivHaarChar_symm`,
`mulEquivHaarChar_eq_one_of_compactSpace`.

**Modular character (Group/ModularCharacter.lean):**
- `Measure.modularCharacterFun (g : G) : ℝ≥0 := haarScalarFactor (map (· * g) haar) haar`
- `Measure.modularCharacter : G →* ℝ≥0` (group hom)
- `map_right_mul_eq_modularCharacterFun_smul`
- `modularCharacterFun_pos`, `modularCharacterFun_map_one`,
  `modularCharacterFun_map_mul`
- **Continuity is a TODO in source.**

**Distribution Haar character (Haar/DistribChar.lean):**
`distribHaarChar : G →* ℝ≥0` for `DistribMulAction G A` with
`μ.IsAddHaarMeasure`. **For the conjugation action of `A` on `N`,
`distribHaarChar N (a) = |det Ad(a)|_𝔫|`.** This is the bridge to
the AN modular character formula.

**Invariant measure / Haar mixin (Group/Measure.lean):**
`IsMulLeftInvariant`, `IsMulRightInvariant`, `IsInvInvariant`,
`Measure.inv`, `IsHaarMeasure`, `measurePreserving_mul_left`/`_right`,
`map_mul_left_eq_self`, `Measure.prod.instIsMulLeftInvariant`,
`prod.instIsHaarMeasure`, `IsHaarMeasure.nnreal_smul`,
`IsHaarMeasure.comap`, `IsHaarMeasure.sigmaFinite`,
`MulEquiv.isHaarMeasure_map`, `ContinuousMulEquiv.isHaarMeasure_map`,
`ContinuousLinearEquiv.isAddHaarMeasure_map`, `IsHaarMeasure.noAtoms`.

**Change of variables (Jacobian.lean):**
- `lintegral_abs_det_fderiv_eq_addHaar_image`:
  `∫⁻ x in s, ‖(f' x).det‖ ∂μ = μ (f '' s)`.
- `map_withDensity_abs_det_fderiv_eq_addHaar`:
  `map f ((μ.restrict s).withDensity ‖det f'‖) = μ.restrict (f '' s)`.
- `restrict_map_withDensity_abs_det_fderiv_eq_addHaar` (restricted).
- `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.
- **`integral_image_eq_integral_abs_det_fderiv_smul` (Bochner version, the workhorse for T1-7).**
- `integral_target_eq_integral_abs_det_fderiv_smul` (for
  `OpenPartialHomeomorph` — directly suited to the Iwasawa
  diffeomorphism).

### Iwasawa-specific closability

| Target | What Mathlib gives | What we must prove |
|--------|---------------------|---------------------|
| `δ(diag a) = ∏_{i<j} aᵢ/aⱼ` | `distribHaarChar` framework; the abstract `modularCharacter` | Determinant of `Ad(a)` on upper-triangular unipotents (matches our T1-6) |
| `det(d iwasawaMap)` | Change-of-variables theorems in Jacobian.lean | The explicit determinant from block structure (matches our T1-5/T1-6) |
| Pushforward of K × A × N Haar to G Haar | `prod.instIsHaarMeasure`, `ContinuousMulEquiv.isHaarMeasure_map`, `Measure.map` + `withDensity` | The diffeomorphism itself (matches T1-2 / T1-3 / T1-4 chain) and the resulting scalar |

The Mathlib machinery for the eventual `T1-7` and Tier 4 steps is in
place. The **gap** is the Iwasawa-specific computation, which is
exactly what T1-5 and T1-6 of this project provide.

---

## Search summary 1: Lean Lie theory papers

Three primary papers found (and one auxiliary):

1. **Nash, "Formalising Lie algebras"** (CPP 2022,
   <https://arxiv.org/abs/2112.04570>). Establishes Mathlib's
   `LieRing`/`LieAlgebra`/`LieSubalgebra`/`LieIdeal`/`LieModule`
   hierarchy, constructs `sl`, `so`, `sp`, exceptional algebras. All
   over arbitrary commutative rings (typeclass-driven, no matrices
   unless explicit). Code is *in Mathlib*, not standalone.

2. **Nash, "Engel's theorem in Mathlib"** (JAR 2023,
   <https://arxiv.org/abs/2304.10424>). Formalizes Engel + lower
   central series + Engel subalgebra. Entry point to root-space theory.
   Maximally general (commutative rings, no characteristic-zero or
   finite-dim hypotheses). Code in Mathlib.

3. **del Barco, Infanti, Rivas, Schwahn, "Formalizing a classification
   theorem for low dimensional solvable Lie algebras in Lean"** (ITP
   2025, <https://arxiv.org/abs/2505.19975>; code at
   <https://github.com/LieLean/LowDimSolvClassification>). Classifies
   solvable Lie algebras of dim ≤ 3 over arbitrary fields. Hybrid
   approach: explicit vector-space calculations + abstract
   `LieSemidirectProduct`, `LieAlgebra.commutator`,
   `LieAlgebra.IsAlmostAbelian`. The `LieSemidirectProduct` is
   directly reusable for the AN part of KAN.

Auxiliary: Andrew Yang PR #13307 (roots form root system), Johan
Commelin PRs #12297/13265/13391/13217 (Cartan subalgebra +
Killing-semisimplicity), now in
`Mathlib.Algebra.Lie.Semisimple.*` and `Mathlib.Algebra.Lie.CartanSubalgebra`.
Kytölä's Virasoro algebra paper (<https://arxiv.org/abs/2510.21741>)
is adjacent but doesn't supply matrix Lie group machinery.

**No formalized Iwasawa decomposition exists anywhere.** No
formalized Cartan involution. No formalized restricted root system.

---

## Search summary 2: Lean Zulip threads

Three primary threads:

1. **"Eigenvalues of Cartan matrices" (#maths,
   <https://leanprover-community.github.io/archive/stream/116395-maths/topic/Eigenvalues.20of.20Cartan.20matrices.html>).**
   Oliver Nash + Damiano Testa + Patrick Massot + Kalle Kytölä +
   Antoine Chambert-Loir + Kevin Buzzard on the Perron-Frobenius
   argument for Cartan matrix eigenvalues. Nash sketched a clean
   `M = 2I - A` argument. No PR opened in-thread.

2. **"Low-dimensional Lie algebras" (#maths,
   <https://leanprover-community.github.io/archive/stream/116395-maths/topic/Low-dimensional.20Lie.20algebras.html>).**
   Paul Schwahn announced 2-dim Lie algebras over arbitrary fields.
   Oliver Nash confirmed nobody else was working on low-dim
   classification and that the semisimple classification project
   (PR #10066) was paused but would resume in 2025.

3. **"Getting the manifold from a Lie group" (#maths,
   <https://leanprover-community.github.io/archive/stream/116395-maths/topic/Getting.20the.20manifold.20from.20a.20Lie.20group.html>).**
   Mr Proof + Yan Yablonovskiy + Michael Rothgang + Jireh Loreaux on
   the forgetful `LieGroup → IsManifold`. Rothgang clarified `LieGroup`
   already extends `IsManifold` (auto-cast). No PR; unresolved: nicer
   notation for the structure projection.

**Name collision warning:** "Discussion on formalization of Iwasawa
Theory in Lean" is Jz Pan's number-theoretic `Z_p`-extension project
(<https://acmepjz.github.io/lean-iwasawa>), NOT the KAN Lie group
Iwasawa decomposition. Don't conflate them.

**Gaps:** no archived Zulip thread on Lie-sense Iwasawa, Cartan
decomposition `g = k + p`, Lie-group adjoint, or modular characters
of LCH groups.

---

## Search summary 3: Mathlib4 GitHub PRs (May 2025 to May 2026)

**Root systems and Cartan matrices** (~15 PRs):
Oliver Nash dominates: #39491 (open) Cartan-matrix eigenvalue ≠ 4,
#38760, #38749 (Cartan criterion), #34727 (Geck Cartan matrix),
#33557 (root base), #33321 (linear-ind roots), #33013, #32922,
#32763 (classical Cartan), #29052, #26965/26849/26819 (Geck reorg),
#25480 (G2), #25285/25214 (Geck construction).

**Killing form and semisimple Lie algebras** (5 PRs):
#36298 (semisimple bases, Nash), #35326 (root space decomp of
ideals, jano-wol), #34856 (Killing-orth complement, jano-wol),
#34584 (semisimple repr, stepan2698-cpu), #27237 (Geck → fd
semisimple, Nash).

**Lie algebra structure (loops, extensions, sl2)** (~10 PRs):
Scott Carnahan + Pinyuan Chen + Leonid Ryvkin work on loops, sl2,
LieDerivations, graded Lie algebras, extensions, 2-cocycles, low-degree
cochains.

**Lie groups, manifolds, Haar** (5 PRs):
- **#37932 (OPEN, idontgetoutmuch, 2026-04-11): exponential map of a
  Lie group is smooth.** Direct interest for T1-4 Lemma 1.
- #33923 (MERGED, Michael Rothgang, 2026-01-13): fix example of GL(V)
  as a Lie group.
- #38773 (MERGED, Yi Yuan, 2026-04-30): cleanup `Haar/Quotient`.
- #32672/32661 (MERGED, Thomas Browning, 2025-12): Haar on short
  exact sequences.

**No PR on Iwasawa decomposition, Cartan involution, or real Lie
groups.** Heather Macbeth, Eric Wieser, Joël Riou do not appear as
primary authors. Oliver Nash for root-system/Cartan-matrix, Scott
Carnahan for loops/extensions, Leonid Ryvkin for Lie-Rinehart and
derivations.

---

## Phase 2 routing decisions

Given the Phase 1 findings, the optimal routes are:

### T1-2 (Gram-Schmidt smoothness, 60 min)
**Route**: Prove `ContDiffOn ℝ ⊤ gramSchmidt {M | M.det ≠ 0}` matrix-level,
then transfer to `G n` via `ContMDiff.of_comp_isOpenEmbedding G_isOpenEmbedding`
(this is the `UnitsOfNormedAlgebra.lean` pattern verbatim). Inner
products are smooth (bilinear → `ContDiff`), normalization is
`Real.contDiffAt_sqrt` on the positivity open set.

### T1-4 Lemma 1 (`mfderiv_leftMul_at`, 30-60 min)
**Route**: Use `contMDiff_mul_left` for smoothness (which gives
`mdifferentiableAt_mul_left` for MDifferentiableAt). For the explicit
mfderiv: `G n`'s chart is `Subtype.val`, so the chart-coord version
is `(Subtype.val) ∘ (g₀ * ·) ∘ (chart_symm) = g₀.val * Subtype.val`.
The matrix-level fderiv of `M ↦ g₀.val * M` is the constant CLM
`X ↦ g₀.val * X`. Combine with our existing `mfderiv_subtypeVal_G = id`
helper. Estimated 30-40 lines.

### T1-4 Lemma 2 (`conjugation_NN_by_diagonal`, 60 min)
**Route**: At matrix level, `Ad(a) X = a * X * a⁻¹`. Use
`HasMFDerivAt.mul'` twice on `(X, a) ↦ a * X` and `(Y, a⁻¹) ↦ Y * a⁻¹`,
plus `mfderiv_const` for the `a, a⁻¹` factors (fixed at the diagonal
point). At the diagonal `a = diag(a₁,...,aₙ)`, the action on a strictly
upper triangular `X` works out to `(Ad(a) X)_{ij} = (aᵢ/aⱼ) X_{ij}`.
The derivative at `X = 0` is the same CLM (since `Ad(a)` is already
linear). 60-80 lines.

### T1-4 Lemma 3 (`mfderiv_iwasawaMap_at`, 90 min)
**Route**: Combine Lemma 1 (left translation) with Lemma 2 (Ad(a)
twist) via the equivariance `iwasawaMap (k₀ k, a₀ a, u₀ u) =
k₀ a₀ u₀ · iwasawaMap (k, Ad(a₀)⁻¹ ... )`. The volume preservation
subtlety: the abstract Lie-group convention (left Haar) requires the
left-invariant frame, while the ambient matrix Jacobian uses the
embedding. **Resolve via the convention chosen in the Iwasawa map**:
our `iwasawaMap` is `(k, a, u) ↦ k.val * a.val * u.val` in matrix
form, so the ambient Jacobian is the appropriate normalization.

### T1-5 (abstract Jacobian determinant, 45 min)
**Route**: `det(d iwasawaMap |_{k,a,u}) = det(Ad(a)|_𝔫) × (KK-factor)`.
Use Lemma 3's structure + block-triangular determinant identity. The
KK-factor is unity once normalizations are right (no scaling factor
from the diagonal A-component because `d(diag) = diagonalCLM`,
trivial determinant on the relevant subspace).

### T1-6 (explicit product, 60 min)
**Route**: From Lemma 2, `(Ad(diag(a))|_NN)` has diagonal entries
`a_i/a_j` indexed by `(i, j)` with `i < j` (one per strictly-upper-
triangular position). Determinant = product over `i < j` of `a_i/a_j`.
This is a `Finset.prod_image` or `Matrix.det_diagonal` computation.

---

## What to NOT depend on

1. Don't try to use Mathlib's `LieGroup.Ad` — it doesn't exist.
2. Don't try to use `LieGroup.exp` — open PR (#37932) not yet merged.
3. Don't expect a closed-form `mfderiv (· * g₀) g` Mathlib lemma — only
   smoothness exists.
4. Don't expect Cartan involution / Cartan decomposition / restricted
   roots infrastructure for Tier 2 — all from scratch.
5. Don't expect `Measure.modularCharacterFun` to be known continuous
   yet (TODO in source).

## What WE can leverage directly

1. **`contMDiff_mul_left`, `mdifferentiableAt_mul_left`** — left-translation smoothness.
2. **`HasMFDerivAt.prodMk`, `mfderiv_prodMk`** — product manifold differential.
3. **`HasMFDerivAt.mul'`** — Leibniz for ring multiplication.
4. **`ContMDiff.of_comp_isOpenEmbedding`** — lift smoothness from ambient algebra.
5. **`mfderiv_extChartAt_self`** — chart derivative at the point is identity (our `mfderiv_subtypeVal_G` is this for `G n`).
6. **`integral_image_eq_integral_abs_det_fderiv_smul`** — change-of-variables for T1-7.
7. **`Measure.modularCharacter`, `Measure.distribHaarChar`,
   `Measure.haarScalarFactor`, `mulEquivHaarChar`** — abstract Haar
   manipulation.
8. **`LieAlgebra.ad_eq_lmul_left_sub_lmul_right`** — `ad` on associative
   algebras (matrix Lie bracket).

---

## File location appendix

Local Mathlib paths:
- `.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/{LieGroup, LeftInvariantDerivation, Monoid, SmoothFunctions}.lean`
- `.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/{Basic, Atlas, SpecificFunctions}.lean`
- `.lake/packages/mathlib/Mathlib/Geometry/Manifold/Diffeomorph.lean`
- `.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/{UnitsOfNormedAlgebra, Sphere}.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Lie/{Basic, Killing, Engel, CartanSubalgebra, Matrix, Classical, OfAssociative, SkewAdjoint}.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Lie/Semisimple/Basic.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Lie/Weights/{Basic, Killing}.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Lie/AdjointAction/{Basic, Derivation}.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Killing.lean`
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/{Basic, OfBasis, Unique, MulEquivHaarChar, DistribChar}.lean`
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Group/{ModularCharacter, Measure}.lean`
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`

More detailed notes on two of the topics are in
`.research/1a_manifold.md` and `.research/1f_github_prs.md`; the rest is
integrated above.

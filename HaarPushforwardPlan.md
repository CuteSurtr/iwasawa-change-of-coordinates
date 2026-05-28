# Haar Pushforward Plan: replacing `iwasawa_haar_pushforward_bridge`

Scope note only. This document plans the work; it proves nothing. It records
the verified state of the project, surveys the Mathlib measure theory API by
name and current signature, isolates the genuine remaining gap, and gives a
dependency ordered lemma list. No Haar proof is started here.

**Status update (2026-05-28).** The placeholder axiom
`iwasawa_haar_pushforward_bridge` was found to be logically redundant: its
statement was only the weak existential in Section 2, which is already proved
without any axiom (`c_n = 1`). It has therefore been removed, and the whole
`iwasawa_change_of_coords/` subtree is now genuinely axiom clean, confirmed by
a fresh `#print axioms`. The genuine measure theoretic identity in Section 2
is still NOT formalized; the lemma list L0 to L9 below remains future work,
with none of L1 to L9 implemented.

All declaration names below were verified against the current source, and
their axiom footprints were checked with `#print axioms` (fresh elaboration,
not a cache replay) on 2026-05-28. Mathlib signatures were read from the
pinned copy under `.lake/packages/mathlib` (`leanprover/lean4:v4.30.0-rc1`).

## 1. What is already in hand (verified, axiom clean)

Every item below depends only on `[propext, Classical.choice, Quot.sound]`.

| Result | Location | Statement (informal) |
|---|---|---|
| `iwasawaDiffeomorph` | `IwasawaDiffeomorph.lean:756` | `K n × A n × UU n ≃ₘ G n` (full `C^∞` diffeomorphism) |
| `mfderiv_iwasawaMap_at_factored` | `IwasawaMFDeriv.lean:1093` | `mfderiv iwasawaMap (k,a,u) = iwasawaMatrixLeibnizCLM k a u` |
| `iwasawaCharted` | `IwasawaComplete.lean:818` | flat single chart map `(X,v,Z) ↦ cayley(X) · diag(e^v) · (Z+1)` |
| `detInIwasawaBases_fderiv_iwasawaCharted_general` | `IwasawaComplete.lean:1434` | signed Jacobian of `iwasawaCharted` at a general point, in the Iwasawa source bases and standard matrix target basis |
| `absDetInIwasawaBases_fderiv_iwasawaCharted_general` | `IwasawaComplete.lean:1446` | its absolute value form |
| `absDetIwasawaMatrixLeibnizCLM_at_factored_unconditional` | `IwasawaComplete.lean:485` | `absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) = 2^{n(n-1)/2} · det(a)^n · det(adNN a)` |
| `adNN_det_eq_pair_product` | `IwasawaJacobianExplicit.lean:1401` | `det(adNN a) = ∏_{i<j} a_i / a_j` |
| `abs_det_skOrthConjCLM_eq_one` | `IwasawaComplete.lean:472` | `|det (skOrthConjCLM k)| = 1` for orthogonal `k` (closes the orthogonality gap) |

The closed form absolute Jacobian of the charted map, at a general chart
point `(X, v, Z)` with `a = expDiagA v`, is

```math
\bigl|\det\bigl(d\,\mathrm{iwasawaCharted}_{(X,v,Z)}\bigr)\bigr|_{\text{Iwasawa bases}}
  = 2^{\,n(n-1)/2}\,|\det a|^{\,n}\,|\det(\mathrm{ad}_{\mathfrak n} a)|\,
    \bigl(|\det(1+X)|^{-1}\bigr)^{\,n-1},
```

with the positive root product

```math
\delta(a) = \det(\mathrm{ad}_{\mathfrak n} a) = \prod_{i \lt j} \frac{a_i}{a_j}.
```

So the geometric and algebraic Jacobian content is complete. The factor
`|det a|^n`, the character `δ(a)`, and the Cayley correction
`(|det(1+X)|^{-1})^{n-1}` are all explicit.

## 2. The former axiom and the real target

`IwasawaBridge.lean` previously declared

```
axiom iwasawa_haar_pushforward_bridge :
    ∃ (c_n : ℝ), 0 < c_n ∧
      ∀ (a : A n), c_n * |LinearMap.det (adNN a).toLinearMap| > 0
```

This weak existential was the only user axiom in the project, consumed only by
`iwasawa_pushforward_weighted_haar_exists`. The existential is trivially true
(`c_n = 1`, every factor `a_i/a_j` is positive), and the identical statement
was already proved without any axiom in `IwasawaComplete.lean`
(`iwasawaHaarBridge`, `iwasawaPushforwardWeightedHaarExists`). The axiom
therefore carried no mathematical content beyond positivity, so it has been
removed and the consumer is now proved directly. The real goal that this plan
still targets is the genuine measure theoretic identity it once stood in for,
namely

```math
\int_G f\,dx = c \int_U \int_A \int_K f(uak)\, \delta(a)^{-1}\, du\, da\, dk
```

for a positive constant `c` and left Haar measures on `K`, `A`, `U`, `G`.

## 3. Mathlib API survey (verified names and signatures)

### 3a. Change of variables (`Mathlib/MeasureTheory/Function/Jacobian.lean`)

Governing context (file lines 104, 252):
`{E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`,
`[NormedAddCommGroup F] [NormedSpace ℝ F]`, and for the integral forms
`[MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]`.

- `integral_image_eq_integral_abs_det_fderiv_smul` (line 1218):
  hypotheses `(hs : MeasurableSet s)`,
  `(hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)`, `(hf : InjOn f s)`,
  `(g : E → F)`; conclusion
  `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`.
- `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (line 1188): the
  `ℝ≥0∞` valued analogue with `g : E → ℝ≥0∞`.
- `integral_target_eq_integral_abs_det_fderiv_smul` (line 1230): for
  `{f : OpenPartialHomeomorph E E}` with
  `(hf' : ∀ x ∈ f.source, HasFDerivAt f (f' x) x)`; conclusion
  `∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ`.
  This is the most convenient entry point for a chart/diffeomorphism.
- `map_withDensity_abs_det_fderiv_eq_addHaar` (line 1132), measure level:
  `Measure.map f ((μ.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)) = μ.restrict (f '' s)`.
- `restrict_map_withDensity_abs_det_fderiv_eq_addHaar` (1156),
  `lintegral_abs_det_fderiv_eq_addHaar_image` (1100),
  `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` (1204).

Critical hypothesis to plan around: `(f' x).det` is
`ContinuousLinearMap.det`, which is defined only for an endomorphism
`f' : E →L[ℝ] E`. So these theorems require source and target to be the
same space `E`. `iwasawaCharted` maps between two different (but equal
dimension) spaces, so it must first be conjugated into a self map of one
fixed Euclidean space by linear isomorphisms (see L2 below). This is exactly
the role of `detInIwasawaBases`, which already takes the determinant after
identifying both sides with fixed bases.

### 3b. Additive Haar from a basis (`Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean`)

- `Basis.addHaar (b : Basis ι ℝ E) : Measure E` (line 254, `irreducible_def`):
  the Lebesgue measure giving the unit parallelepiped of `b` measure `1`.
- instance `isAddHaarMeasure_addHaar` (it is an `IsAddHaarMeasure`),
  `Basis.addHaar_self`, `Basis.prod_addHaar` (product of bases gives the
  product measure), `Basis.addHaar_reindex`.

This is how to put a concrete `IsAddHaarMeasure` on each chart model:
`Sk n` (via `skBasis`), `Fin n → ℝ` (Pi basis), `NN n` (via `nnBasis`),
and the target `Matrix (Fin n) (Fin n) ℝ` (standard basis). These are the
same bases used by `detInIwasawaBases`, so the chart Jacobian already lines
up with these measures.

### 3c. Additive Haar under linear maps (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`)

Same context as 3a. These give the `|det|` scaling, needed for every basis
change and for the `GL_n` density.

- `map_linearMap_addHaar_eq_smul_addHaar` (line 234):
  `{f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0)` implies
  `Measure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ`.
- `addHaar_image_linearMap (f : E →ₗ[ℝ] E) (s)` (300):
  `μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s`.
- `addHaar_image_continuousLinearMap` (315), and the preimage variants
  `addHaar_preimage_linearMap` (264), `addHaar_preimage_continuousLinearMap`
  (276), `addHaar_preimage_linearEquiv` (284),
  `addHaar_preimage_continuousLinearEquiv` (293).

### 3d. Group Haar (`Haar/Basic.lean`, `Group/Measure.lean`)

- `haarMeasure (K₀ : PositiveCompacts G) : Measure G` (`Basic.lean:517`),
  instance `isHaarMeasure_haarMeasure` (570).
- `class IsHaarMeasure` (`Group/Measure.lean:770`), `IsAddHaarMeasure` (757).
- `prod.instIsHaarMeasure` (910): a product of Haar measures is Haar.
- `ContinuousLinearEquiv.isAddHaarMeasure_map` (892), and the group level
  `MulEquiv.isHaarMeasure_map`, `ContinuousMulEquiv.isHaarMeasure_map`
  (pushforward of Haar under a topological isomorphism is Haar).
- `IsAddHaarMeasure.domSMul` (937): a conjugation scaled additive Haar
  measure is again additive Haar (the basis for `distribHaarChar`).

### 3e. Haar scalar character (`Haar/MulEquivHaarChar.lean`, `Haar/DistribChar.lean`)

- `mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0` (`MulEquivHaarChar.lean:40`): the
  scalar by which a continuous multiplicative automorphism scales Haar.
- `distribHaarChar (A) : G →* ℝ≥0` (`DistribChar.lean:43`): for a
  `DistribMulAction G A` with additive Haar on `A`, defined via
  `addHaarScalarFactor (DomMulAct.mk g • addHaar) addHaar`.

For the conjugation action of `A` on `N`, the standard identity is
`distribHaarChar (NN n) a = |det (adNN a)|`, which our
`adNN_det_eq_pair_product` then evaluates to `∏_{i<j} a_i/a_j`. The exact
name of the determinant specialization lemma in Mathlib was not pinned down
in this pass (the `grep` for theorem bodies in `MulEquivHaarChar.lean` and
`DistribChar.lean` returned only the `def`s). To confirm before relying on
it: search for `addHaarScalarFactor` of a `ContinuousLinearMap` equaling
`|det|`, which should follow from `map_linearMap_addHaar_eq_smul_addHaar`.

### 3f. Not in Mathlib (must be built)

Confirmed absent by search in this pass:

- No Haar measure on `GL_n(ℝ)` or on matrix units; in particular the
  identity `haar_G = |det g|^{-n} · volume` is not present.
- No multiplicative Haar on `(0, ∞)` (the one dimensional `dt/t`), and no
  `exp`/`log` measure preserving statement that would hand us the `A` group
  Haar in log coordinates for free.

These two are the genuinely new measure theoretic pieces.

## 4. The real gap

The geometric Jacobian is done. The gap is the bridge between Haar measure
on each group and additive (Lebesgue) Haar in the relevant charts, plus the
bookkeeping of constants.

1. The Mathlib change of variables theorem is stated for an additive Haar
   measure `μ` (`IsAddHaarMeasure`) on a finite dimensional real normed space
   `E`, applied to a self map `E → E`. Our objects are multiplicative groups
   (`K = O(n)` compact, `A` positive diagonal, `U` unipotent, `G = GL_n`),
   and the wanted measures are their left Haar measures. Each Haar measure
   must first be written in its chart as a weighted `Basis.addHaar` measure.

2. Each chart introduces its own Jacobian and normalizing constant:
   - `A`: the log chart `A.toFinNRHomeomorph` should send multiplicative
     Haar to Lebesgue on `Fin n → ℝ` (the classical `dt/t = d(log t)`), so in
     this chart `haar_A` is `Basis.addHaar` up to a constant. No Mathlib
     support found, so this identification must be proved (or `haar_A` simply
     defined as the chart pushforward of Lebesgue, deferring invariance).
   - `U`: unipotent, so left translation is affine with determinant `1` in
     the strictly upper coordinates; `haar_U` equals `Basis.addHaar` on
     `NN n` via `UU.toNNHomeomorph` with constant `1`. Relatively clean.
   - `K`: compact, `haar_K` finite. In the Cayley / sphere pattern atlas the
     Cayley chart has a smooth positive Jacobian; the multi chart atlas means
     either a partition of unity argument or the observation that the chart
     complement has measure zero. The whole `K` contribution is a finite
     constant absorbed into `c`.
   - `G`: the open subgroup chart is `Subtype.val` into
     `Matrix (Fin n) (Fin n) ℝ`. Here `haar_G = |det g|^{-n} · volume`, which
     introduces the `|det g|^{-n}` factor. This is the crucial non chart
     constant and is not in Mathlib.

3. The charted Jacobian `detInIwasawaBases` is taken in fixed source and
   target bases. Relating it to a ratio of Haar densities means tracking how
   the product `Basis.addHaar` on `Sk × (Fin n → ℝ) × NN` and the
   `Basis.addHaar` on `Matrix` differ from the actual group Haar measures.
   The constants from `map_linearMap_addHaar_eq_smul_addHaar` and the `K`,
   `A`, `U`, `G` normalizations all collect into the single constant `c`.

4. The exponent arithmetic that produces `δ(a)^{-1}`: at `g = kau`,
   `|det g| = |det a|` (since `|det k| = 1`, `det u = 1`). The `G` Haar
   factor `|det g|^{-n} = |det a|^{-n}` multiplies the Jacobian factor
   `|det a|^n · |det(adNN a)|`, cancelling `|det a|^n` and leaving
   `|det(adNN a)| = δ(a)`. Whether `δ(a)` or `δ(a)^{-1}` appears in the final
   formula depends on the direction (pushforward of the product measure to
   `G`, versus disintegration of `haar_G`); the standard `dg = dk · δ(a) · da · dn`
   convention yields `δ(a)^{-1}` in the `∫_G f` form above. This sign of the
   exponent must be tracked carefully.

## 5. Dependency ordered lemma list

Difficulty key: `[clean]` is a direct Mathlib application or plumbing;
`[medium]` needs a real but routine argument; `[hard]` is genuinely new
mathematics or fills a Mathlib gap.

- L0 (have): the Section 1 results.
- L1 `[clean]`: install `Basis.addHaar` measures on `Sk n`, `Fin n → ℝ`,
  `NN n`, and `Matrix (Fin n) (Fin n) ℝ`, with `IsAddHaarMeasure` instances;
  form the product additive Haar on `Sk × (Fin n → ℝ) × NN`
  (`Basis.prod_addHaar` or `Measure.prod`). Mathlib: 3b.
- L2 `[medium]`: conjugate `iwasawaCharted` into a self map
  `Ψ : ℝ^{n²} → ℝ^{n²}` (or of `Matrix`) by the source and target basis
  isomorphisms, and prove `ContinuousLinearMap.det (fderiv Ψ x)` equals the
  `detInIwasawaBases` value already computed. Mostly unfolding the definition
  of `detInIwasawaBases`; this is the device that makes 3a applicable.
- L3 `[medium]`: apply `integral_target_eq_integral_abs_det_fderiv_smul`
  (or `integral_image_...`) to `Ψ`. Discharge `InjOn` from
  `iwasawaDiffeomorph`, `HasFDerivAt` on the source from
  `differentiableOn_iwasawaCharted` plus the chain rule through the linear
  isos, and `MeasurableSet` of the chart domain. Mathlib: 3a.
- L4 `[medium]`: transport L3 back to the chart model spaces, absorbing the
  determinants of the basis isos via `addHaar_image_linearMap` /
  `map_linearMap_addHaar_eq_smul_addHaar`. Output: an integral identity over
  `Matrix`-addHaar versus product-addHaar with the explicit
  `|detInIwasawaBases|` weight, up to a constant. Mathlib: 3c.
- L5 `[hard]`: define `haar_G` on `G = GL_n(ℝ)` and prove
  `haar_G = |det g|^{-n} · volume` (equivalently, that `|det g|^{-n} dλ` is
  left and right invariant). Left translations are linear on `Matrix`, so
  `map_linearMap_addHaar` plus multiplicativity of `det` drives this, but the
  statement and the unimodularity corollary are not in Mathlib. Mathlib
  support: 3c for the linear pushforward; the assembly is new.
- L6 `[hard for A, medium for U]`: identify `haar_A` with Lebesgue in the
  log chart (needs the multiplicative `dt/t` fact, not in Mathlib), and
  `haar_U` with `Basis.addHaar` on `NN n` (left translation determinant `1`).
  A pragmatic alternative: define `haar_A` and `haar_U` as the chart
  pushforwards of `Basis.addHaar` and prove left invariance directly,
  sidestepping a generic multiplicative Haar theory.
- L7 `[medium]`: handle the compact factor `K`. Relate the atlas pushforward
  of `haar_K` to `Basis.addHaar` on `Sk n`; conclude the `K` contribution is
  a finite positive constant. Multi chart bookkeeping (measure zero
  complement or partition of unity).
- L8 `[medium]`: combine L4 with L5, L6, L7. Use `|det(kau)| = |det a|` to
  turn the `G` Haar factor `|det a|^{-n}` against the Jacobian `|det a|^n`,
  leaving `δ(a)`; reconcile the exponent direction to land on `δ(a)^{-1}`;
  collect all chart and basis constants into one positive `c`. This is the
  numerical heart and is mostly careful algebra once L1 to L7 exist.
- L9 `[clean]`: state the final theorem
  `∫_G f dx = c ∫_U ∫_A ∫_K f(uak) δ(a)^{-1} du da dk`, replace the axiom in
  `IwasawaBridge.lean`, and update `iwasawa_pushforward_weighted_haar_exists`
  to consume the real statement. Optionally connect `δ(a)` to
  `distribHaarChar (NN n) a` via 3e and `adNN_det_eq_pair_product` for the
  abstract modular character phrasing.

## 6. Risks and items to confirm before coding

- Confirm the exact Mathlib names for the `distribHaarChar` to `|det|`
  specialization and the `mulEquivHaarChar` integral lemmas (3e); the `grep`
  in this pass found the `def`s but not the theorem bodies.
- L5 and L6 are the load bearing new pieces. If `haar_G = |det g|^{-n} volume`
  proves heavy, the disintegration route (Section 4) via `distribHaarChar`
  and Haar uniqueness (`measure_isHaarMeasure_eq_smul_of_isOpen` and friends
  in `Haar/Unique.lean`) is the main alternative, trading explicit chart work
  for abstract invariance and uniqueness arguments.
- The change of variables theorems force source equal to target; do not skip
  L2, or `ContinuousLinearMap.det` will not typecheck on `fderiv iwasawaCharted`.
- Unimodularity of `GL_n` (left Haar equals right Haar) is implicitly used by
  the `f(uak)` ordering; budget a lemma for it.
- Keep `c` symbolic until the very end; every chart and basis normalization
  feeds it, and pinning a numeric value early invites sign and exponent
  mistakes.

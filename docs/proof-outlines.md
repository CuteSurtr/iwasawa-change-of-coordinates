# Milestone proof outlines

> Detailed reference for the [Iwasawa Decomposition and Change of Coordinates](../README.md) project. This page is long and dense with math, so GitHub may show it as source rather than rendering every formula. The short overview, with rendered status, is in the [README](../README.md).

## Proof outlines

### Milestone 1: Iwasawa bijection

The equivalence `iwasawaEquiv : K × A × UU ≃ G` reuses the parent
project's existence (`Iwasawa.exists_iwasawa`) and uniqueness
(`Iwasawa.iwasawa_unique`).

* Forward: $`(k, a, u) \mapsto \langle k \cdot a \cdot u, \_ \rangle`$, with $`\det(kau) \ne 0`$ from the
  three component invertibility lemmas.
* Backward: take the Iwasawa factorization `F := Iwasawa.iwasawa g.2`
  and return its $`(k, a, u)`$ components as subtypes.
* `right_inv` is `F.factorization.symm`.
* `left_inv` builds an explicit `IwasawaFactorization (kau)` from
  $`(k, a, u)`$ and applies `Iwasawa.iwasawa_unique`.

### Milestone 1b: Convention swap and Cartan involution

`inv_iwasawa_jl` is a direct algebraic identity:

```math
\begin{aligned} (k \cdot a \cdot u)^{-1} &= u^{-1} \cdot (k \cdot a)^{-1} && (\texttt{Matrix.mul\_inv\_rev}) \\ &= u^{-1} \cdot a^{-1} \cdot k^{-1} && (\texttt{Matrix.mul\_inv\_rev}, \texttt{mul\_assoc}) \\ &= u^{-1} \cdot a^{-1} \cdot k^T && (\texttt{IsOrthogonal.matInv\_eq\_transpose}) \end{aligned}
```

`cartanInvolution g := ⟨(g.1)ᵀ⁻¹, _⟩` requires showing
$`\det((g.1)^T)^{-1} \ne 0`$, which follows from
$`g.1^T \cdot (g.1^T)^{-1} = 1`$ via `Matrix.mul_nonsing_inv` and
taking determinants.

`cartanInvolution_involutive` reduces to
$`(((g.1)^T)^{-1})^{T-1} = g.1`$ via the rewrite chain
`Matrix.transpose_nonsing_inv → Matrix.transpose_transpose →
Matrix.nonsing_inv_nonsing_inv`.

### Milestone 2: Topology and Gram-Schmidt continuity

`continuous_iwasawaMap` is one rule of `Continuous.matrix_mul` lifted
through subtype embeddings.

`continuous_iwasawaSymm` is the substantial piece. It reduces to
continuity of the parent project's Gram-Schmidt derived `qMat`, `dMat`,
`uMat` on `G n`, which in turn reduces to continuity of `gramSchmidt`
and `gramSchmidtNormed` (Mathlib's
`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`) in the input
function, on the locus of linearly independent column families.
Mathlib v4.30 does not package this continuity, so we prove it inline:

* `continuous_gCol_at`: column extraction is continuous.
* `continuous_gramSchmidt_at`: by well founded induction on $`i : \mathrm{Fin}\,n`$.
  Inductive step: rewrite via `gramSchmidt_def` to
  `gCol g.1 i − ∑ j ∈ Iio i, (ℝ ∙ gramSchmidt _ j).starProjection (gCol _ i)`.
  The 1D projection becomes the rational expression
  $`(\langle v, w \rangle / \lVert v \rVert^2) \cdot v`$ via `Submodule.starProjection_singleton`, which
  is continuous because the denominator is nonzero on `G n`
  (`gramSchmidt_ne_zero` applied to `Iwasawa.gCol_linearIndependent`).
* `continuous_gramSchmidtNormed_at`: division by nonzero norm.
* `continuous_qMat_subtype`, `continuous_rMat_subtype`,
  `continuous_dMat_subtype`, `continuous_diagInv_dMat_subtype`,
  `continuous_uMat_subtype`: entry wise continuity of the four matrix
  factors built from Gram-Schmidt outputs.
* `continuous_iwasawaSymm` assembles the three factors.

This is the kind of result that could plausibly be upstreamed to
Mathlib (continuity of `gramSchmidt` and `gramSchmidtNormed` in their
input function, on the linearly independent locus); see
`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho` as the natural
home.

### Milestone 3: Smooth structures

Open submanifold smoothness on `G n` is direct: `G n` is open in
`Matrix (Fin n) (Fin n) ℝ` (preimage of $`\ne 0`$ under continuous $`\det`$),
so `IsOpenEmbedding.singletonChartedSpace` and
`IsOpenEmbedding.isManifold_singleton` apply. The norm on Matrix is
chosen via `attribute [local instance]` over
`Matrix.normedAddCommGroup` and `Matrix.normedSpace` (Mathlib
intentionally does not register a global matrix norm because several
natural choices exist).

`UU n` is modeled on `NN n` (the strictly upper triangular `Submodule`)
via the homeomorphism `UU.toNNHomeomorph U := U − 1`. The chart is
single (covers all of `UU n`) and gives `ChartedSpace` and `IsManifold`
instances via `OpenPartialHomeomorph.singletonChartedSpace`.

`A n` is modeled on `Fin n → ℝ` via `A.toFinNRHomeomorph D := (log D_{ii})_i`
with inverse $`v \mapsto \mathrm{diag}(\exp v)`$, giving a single chart smooth structure.

### Milestone 3: Cayley transform on $`O(n)`$

The major mathematical work. The Cayley transform

```math
\mathrm{cayley}\,X = (1 - X)(1 + X)^{-1}
```

parametrizes $`SO(n)`$ minus a measure zero set (the orthogonal matrices with
eigenvalue $`-1`$) by skew symmetric matrices. It never reaches the other
component of $`O(n)`$: an orthogonal $`Q`$ with $`\det Q = -1`$ always has $`-1`$ as
an eigenvalue. The full chain:

* `one_add_skew_isUnit` ($`1 + X`$ invertible for $`X`$ skew). Proof:
  $`(1 + X)(1 - X) = 1 + X \cdot X^T`$ (using $`X^T = -X`$), and
  $`1 + X \cdot X^T`$ is positive definite ($`1`$ is `PosDef`, $`X \cdot X^T`$ is
  `PosSemidef` via `posSemidef_self_mul_conjTranspose`). Hence
  $`(1 + X)(1 - X)`$ is a unit, so $`1 + X`$ is too (via
  `isUnit_of_mul_isUnit_left`).
* `cayley_isOrthogonal`: $`(\mathrm{cayley}\,X)(\mathrm{cayley}\,X)^T = 1`$ for $`X`$ skew, by
  algebraic manipulation using the commutativity of $`(1 + X)`$ and
  $`(1 - X)`$ (and their inverses).
* `cayley_self_inverse`: for any $`X`$ with $`1 + X`$ invertible,
  $`\mathrm{cayley}(\mathrm{cayley}\,X) = X`$. The proof shows
  $`1 - \mathrm{cayley}\,X = X \cdot (1 + \mathrm{cayley}\,X)`$ by post multiplying both sides by
  $`(1 + X)`$ and using the algebraic identities
  $`(1 - \mathrm{cayley}\,X)(1 + X) = X + X`$ and $`(1 + \mathrm{cayley}\,X)(1 + X) = 1 + 1`$.
  Specializations give the left and right inverses
  `cayleyInv_cayley` (on `Sk n`) and `cayley_cayleyInv` (on the
  invertibility set).
* `cayleyInv_isSkew`: for orthogonal $`Q`$ with $`1 + Q`$ invertible,
  $`\mathrm{cayleyInv}\,Q`$ is skew symmetric. The proof uses
  $`Q^T = Q^{-1}`$ (orthogonality) plus the identity
  $`(1 + Q^{-1}) = Q^{-1} \cdot (1 + Q)`$, the commutativity of polynomials in $`Q`$,
  and direct computation of the transpose.
* `cayleyEquiv : Sk n ≃ K_open n` bundles the bijection.
* `continuous_cayley_on_skew` and `continuous_cayleyInv_on_KOpen` use
  Mathlib's `continuousAt_matrix_inv` (for the matrix inverse) and
  `NormedRing.inverse_continuousAt` (for `Ring.inverse` on units).
* `cayleyHomeomorph` bundles topological bijection.
* `instChartedSpaceKOpen`, `instIsManifoldKOpen`: `K_open n` is a
  smooth manifold modeled on `Sk n` via the Cayley chart, set up using
  `IsOpenEmbedding.singletonChartedSpace` on `cayleyHomeomorph.symm`.
* `contMDiff_cayleyHomeomorph`, `contMDiff_cayleyHomeomorphSymm`:
  smoothness in both directions, using `contMDiff_isOpenEmbedding` and
  `contMDiffOn_isOpenEmbedding_symm` plus the function equality
  identification of `cayleyHomeomorph` with the
  `OpenPartialHomeomorph` inverse via
  `IsOpenEmbedding.toOpenPartialHomeomorph_left_inv`.
* `cayleyDiffeomorph` is the bundled $`C^\infty`$ diffeomorphism.

### Milestone 3: Multi chart atlas (Sphere pattern)

The single Cayley chart at the identity covers $`K_{\mathrm{open}}\,n`$ (the open
dense subset of $`SO(n)`$ where $`-1`$ is not an eigenvalue of $`Q`$). To
cover the rest of $`O(n)`$, including the whole $`\det = -1`$ component, we follow Mathlib's pattern from
[`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html)
(stereographic projection from each unit vector, due to Heather Macbeth,
2021) and put a chart at every point.

* `IsOrthogonal.mul`: group closure of $`K`$.
* `K_open_at Q₀`: translated open subset
  $`\{ Q \in K \mid (1 + Q \cdot Q_0^T).det.\mathrm{IsUnit} \}`$.
* `cayleyEquivAt Q₀ : Sk n ≃ K_open_at Q₀`: set level bijection,
  proved by reduction to the identity centered case using
  `cayleyEquiv.symm` and right multiplication by $`Q_0`$ or $`Q_0^T`$.
* `self_mem_K_open_at`: for any $`Q \in K\,n`$, $`Q \in K_{\mathrm{open\,at}}\,Q`$ (since
  $`Q \cdot Q^T = 1`$ and $`1 + 1`$ has invertible determinant $`2^n`$).
* `cayleyOpenChartAt Q₀`: bundles each translated equivalence as an
  `OpenPartialHomeomorph (K n) (Sk n)`. The construction goes through
  `(cayleySourceAt Q₀).openPartialHomeomorphSubtypeCoe.symm.trans
  cayleyChartHomeomorphAt Q₀.toOpenPartialHomeomorph`, avoiding the
  if then else and decidability issues that arise if one tries to define
  the chart's `toFun` globally.
* `instChartedSpaceK`: full atlas on `K n`, with one translated
  Cayley chart at each point.

### Milestone 4: Cartan Lie decomposition

`IsCompl (Sym n) (Sk n)` splits into

* *Disjoint*: $`M \in \mathrm{Sym} \cap \mathrm{Sk} \implies M^T = M = -M \implies 2 \cdot M = 0 \implies M = 0`$.
* *Codisjoint*: $`M = \tfrac{1}{2}(M + M^T) + \tfrac{1}{2}(M - M^T)`$.

### Milestone 5: Iwasawa Lie decomposition

Pairwise disjoint:
* `disjoint_AA_NN`: diagonal $`\cap`$ strictly upper $`= 0`$.
* `disjoint_KK_AA`: skew symmetric diagonal forces all entries zero.
* `disjoint_KK_NN`: case split below, on, and above the diagonal.

`iwasawa_codisjoint` ($`\mathfrak{k} \sqcup \mathfrak{a} \sqcup \mathfrak{n} = \top`$) is the explicit decomposition

```math
M = K + A + N
```

with

```math
A_{ij} = \begin{cases} M_{ii} & \text{if } i = j \\ 0 & \text{else} \end{cases} \quad (\text{in } \mathfrak{a})
```

```math
K_{ij} = \begin{cases} M_{ij} & \text{if } j \lt i \\ -M_{ji} & \text{if } i \lt j \\ 0 & \text{if } i = j \end{cases} \quad (\text{in } \mathfrak{k}, \text{ skew symmetrized})
```

```math
N_{ij} = \begin{cases} M_{ij} + M_{ji} & \text{if } i \lt j \\ 0 & \text{otherwise} \end{cases} \quad (\text{in } \mathfrak{n}, \text{ strict upper})
```

Verification is entry by entry on the trichotomy $`j \lt i`$, $`j = i`$, $`i \lt j`$.

`iwasawaLieDecomp` bundles the four conditions.

`iwasawaLieMap` and `iwasawaLieEquiv` is the linear sum map
$`(X, Y, Z) \in \mathfrak{k} \times \mathfrak{a} \times \mathfrak{n} \mapsto X + Y + Z`$. Surjectivity is
`iwasawa_codisjoint`. Injectivity is the entry wise argument:

* $`j \lt i`$: $`Y_{ij} = 0`$ (off diagonal), $`Z_{ij} = 0`$ ($`j \le i`$), so $`X_{ij} = 0`$.
* $`j = i`$: $`X_{ii} = -X_{ii}`$ (skew) gives $`X_{ii} = 0`$; same for $`Y`$, $`Z`$.
* $`i \lt j`$: by the previous case at $`(j, i)`$ we have $`X_{ji} = 0`$; skew
  gives $`X_{ij} = -X_{ji} = 0`$, then $`Y_{ij} = 0`$ (off diagonal), $`Z_{ij} = 0`$.

This is the algebraic content of "the differential of the Iwasawa map
at the identity is invertible," realized as a `LinearEquiv`.

### Milestone 6: Jacobian determinant (Sylvester-Franke)

`det_sandwichOnSkCLM` ($`\det(\mathrm{sandwich}(B)) = (\det B)^{n-1}`$ on $`\mathrm{Sk}_n`$) is
the $`k = 2`$ case of the Sylvester-Franke identity
$`\det(\Lambda^k B) = (\det B)^{\binom{n-1}{k-1}}`$, via the isomorphism
$`\mathrm{Sk}_n \cong \Lambda^2(\mathbb{R}^n)`$. The proof reduces $`B`$ to a product of
elementary matrices (`Matrix.TransvectionStruct`): the determinant is multiplicative
in $`B`$ (`sandwichOnSkCLM_mul`), equals $`(\det D)^{n-1}`$ on diagonals
(`det_sandwichOnSkCLM_diagonal`, where the operator is diagonal in the `skBasis`),
and equals $`1`$ on transvections (`det_sandwichOnSkCLM_transvection`, unipotent). The
general Jacobian `detInIwasawaBases_fderiv_iwasawaCharted_general` then assembles the
three block determinants of the charted derivative (`sandwichOnSkCLM ((1+X)⁻¹)` on the
$`K`$ block, the identity on $`A`$, and the unipotent `nnRightInvCLM` on $`U`$), giving
$`2^{\binom n 2}(\det a)^n\det(\mathrm{Ad}(a)|_{\mathfrak{n}})\,(\det(1+X))^{-(n-1)}`$.

### Milestone 7: the measure layer

The unimodularity, the conjugation crux, the factor identifications, the $`K`$ Cayley
chart density, and the polynomial null lemma are proved in detail in the
[Haar measure layer](mathematics.md#the-haar-measure-layer-from-the-pointwise-jacobian-to-the-invariant-measure)
section (subsections 10 to 14). In one line each:

- `modularCharacterFun_eq_one`: the $`|\det g|^{-n}`$ weighted coordinate Haar is both
  left and right invariant (each translation is linear with determinant
  $`(\det g_0)^n`$, cancelled by the density), so $`GL_n(\mathbb{R})`$ is unimodular.
- `map_conjAut_haarN`: `conjAut a` is $`u \mapsto a^{-1} u a`$. In the entry chart it is
  the diagonal linear map $`Z \mapsto a^{-1} Z a`$, of determinant $`\delta(a)^{-1}`$, and a
  linear map scales Lebesgue measure under pushforward by the inverse of its
  determinant, so $`(\mathrm{conjAut}\,a)_*\mathrm{haar}_N = \delta(a)\,\mathrm{haar}_N`$.
- `det_cayleyDerivOnSk`: the left translated Cayley derivative on $`\mathrm{Sk}_n`$ is
  $`-2\cdot\mathrm{sandwichOnSkCLM}((1+X)^{-1})`$, so its determinant is
  $`(-2)^{\binom n 2}(\det(1+X))^{-(n-1)}`$ by `det_sandwichOnSkCLM`.
- `volume_setOf_eval_eq_zero`: induction on the number of variables via `finSuccEquiv`,
  with a null base set from the leading coefficient and finite one variable slices,
  assembled by Fubini (`measure_prod_null`).

### Milestone 8: the integration formula

`map_iwasawaMap_haar` in `IwasawaIntegration.lean`, by Haar uniqueness on $`K \times B`$
with $`B = AU`$ (details in [mathematics.md, section 15](mathematics.md#15-the-integration-formula-iwasawaintegrationlean)):

- `BB`, `toBBHomeomorph`: $`B`$ is a subgroup of $`G`$, homeomorphic to $`A \times U`$.
- `kbHomeomorph`, `kbHomeomorph_mul`: $`(k, b) \mapsto k b^{-1}`$ identifies $`K \times B`$
  with $`G`$ and turns left multiplication by $`(k_0, b_0)`$ into $`g \mapsto k_0 g b_0^{-1}`$.
- `instIsHaarMeasure_haarKB`: the pullback of $`\mathrm{haar}_G`$ is a Haar measure on
  $`K \times B`$ (unimodularity of $`G`$ handles the right multiplication).
- `map_rightMulAU_haarAU`: in coordinates $`(a, u)`$, right multiplication on $`B`$ is
  $`(a, u) \mapsto (aa', (a'^{-1}ua')u')`$; it multiplies $`\delta(a)\,da`$ by
  $`\delta(a')^{-1}`$ and $`du`$ by $`\delta(a')`$, so $`\delta(a)\,da\,du`$ is invariant.
- `instIsMulLeftInvariant_candKB`, `candKB_eq_smul_haarKB`: the candidate measure is left
  invariant, hence a multiple of the pullback of $`\mathrm{haar}_G`$.
- `map_iwasawaMapJL_haar`: the $`uak`$ order follows by inversion, using that the Haar
  measures of $`G`$, $`U`$, $`K`$ (unimodular) and $`A`$ (abelian) are inversion invariant.
- `modularCharacterFun_toBB`: $`\delta(a)\,da\,du`$ carried to $`B`$ is a Haar measure on $`B`$,
  and right multiplication by $`a`$ scales it by $`\delta(a)`$, which is the modular
  character by definition.

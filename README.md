# The Iwasawa change of coordinates on $`GL_n(\mathbb{R})`$ in Lean

[![build](https://github.com/CuteSurtr/iwasawa-change-of-coordinates/actions/workflows/build.yml/badge.svg)](https://github.com/CuteSurtr/iwasawa-change-of-coordinates/actions/workflows/build.yml)

This is the follow-up to my [Iwasawa decomposition](https://github.com/CuteSurtr/Iwasawa_Decomposition)
project. That one proves every invertible real matrix factors uniquely as
$`g = kau`$ with $`k`$ orthogonal, $`a`$ positive diagonal and $`u`$ upper unipotent.
Here I prove the stronger statement Jorgenson and Lang make in Theorem 1.1 of
*Spherical Inversion on* $`SL_n(\mathbb{R})`$ (Chapter I): the product map

```math
\Phi : K \times A \times U \to GL_n(\mathbb{R}), \qquad (k, a, u) \mapsto kau
```

is a diffeomorphism, so $`(k, a, u)`$ are global coordinates on $`GL_n(\mathbb{R})`$.
I also prove the formula these coordinates are mostly used for: Haar measure on
$`GL_n(\mathbb{R})`$, written in them, is

```math
\int_{GL_n(\mathbb{R})} f(g)\, dg \;=\; c \int_K \int_A \int_U f(kau)\, \delta(a)\, du\, da\, dk,
\qquad \delta(a) = \prod_{i<j} \frac{a_i}{a_j},
```

for a constant $`c \gt 0`$, where $`dk`$, $`da`$, $`du`$ are Haar measures on the three
factors and $`a = \mathrm{diag}(a_1, \dots, a_n)`$.

Everything builds against a pinned Mathlib with no `sorry`, and every result
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What's proved

Here $`K = O(n)`$, $`A`$ is the positive diagonal matrices and $`U`$ the upper
unipotent ones. The Lean names below live in the `IwasawaCoC` and
`IwasawaCoC.Complete` namespaces.

The map is a bijection (`iwasawaEquiv`), a homeomorphism (`iwasawaHomeomorph`) and
a diffeomorphism (`iwasawaDiffeomorph`). Continuity of the inverse comes down to
Gram-Schmidt being continuous on linearly independent families, which Mathlib
doesn't have, so it's proved by hand in `IwasawaCoC.lean`. Most of the work in the
smooth part is the manifold structure on $`O(n)`$: a Cayley chart
$`X \mapsto (1 - X)(1 + X)^{-1}`$ from skew-symmetric matrices, translated to
every point of $`O(n)`$ the way Mathlib builds its atlas on the sphere.

The derivative of $`\Phi`$ at the identity, in the Cayley, log and translation
charts, is $`(X, v, Z) \mapsto -2X + \mathrm{diag}(v) + Z`$
(`iwasawaMap_mfderiv_at_one_eq_lieEquiv`). The $`-2`$ is the first-order term of
the Cayley map. The derivative at a general point is
`mfderiv_iwasawaMap_at_factored`, and its determinant in these charts is

```math
2^{n(n-1)/2}\,(\det a)^n\,\delta(a)\,\det(1 + X)^{-(n-1)}
```

(`absDetInIwasawaBases_fderiv_iwasawaCharted_general`). The last factor comes from
the Sylvester-Franke identity $`\det(X \mapsto B^T X B) = (\det B)^{n-1}`$ on
skew-symmetric matrices (`det_sandwichOnSkCLM`).

On the Lie algebra side there is $`\mathfrak{gl}_n = \mathfrak{k} \oplus \mathfrak{a} \oplus \mathfrak{n}`$
(`iwasawaLieDecomp`, `iwasawaLieEquiv`), the Cartan splitting
$`\mathfrak{gl}_n = \mathrm{Sym}_n \oplus \mathrm{Sk}_n`$ (`cartanLieDecomp`), and the
refinement $`\mathrm{Sym}_n = \mathfrak{a} \oplus \{X + X^T : X \in \mathfrak{n}\}`$
(`sym_eq_aa_sup_nnSym`, `disjoint_AA_NNsym`).

The measure theory is in `IwasawaHaar.lean` and `IwasawaIntegration.lean`.
$`GL_n(\mathbb{R})`$, $`U`$ and $`K`$ are unimodular (`modularCharacterFun_eq_one`,
`modularCharacterFun_UU_eq_one`, `modularCharacterFun_K_eq_one`). In matrix
coordinates, Haar measure on $`GL_n(\mathbb{R})`$ is Lebesgue measure with density
$`|\det g|^{-n}`$, up to a constant (`nuG_eq_haarScalarFactor_smul_haarG`, and
`haarG_lintegral_eq_smul_setLIntegral_coord` for integrals). Pushing Haar
measure on $`U`$ forward along $`u \mapsto a^{-1} u a`$ multiplies it by $`\delta(a)`$
(`map_conjAut_haarN`). The integration formula above is `map_iwasawaMap_haar` as an
identity of measures and `lintegral_iwasawa` as an integral formula. In
Jorgenson and Lang's order $`g = uak`$ the weight flips to $`\delta(a)^{-1}`$
(`map_iwasawaMapJL_haar`). And $`\delta`$ really is the modular function of the
group $`B = AU`$: Mathlib's `Measure.modularCharacterFun` for $`B`$ takes the value
$`\delta(a)`$ at $`a`$ (`modularCharacterFun_toBB`).

Two smaller results that might be useful elsewhere. The Jacobian of the Cayley chart,
measured against a left-invariant frame, is $`(-2)^{n(n-1)/2}\det(1 + X)^{-(n-1)}`$
(`det_cayleyDerivOnSk`, checked against $`SO(2)`$), which is the density Haar measure on
$`SO(n)`$ has in Cayley coordinates. And the zero set of a nonzero real polynomial in
several variables has Lebesgue measure zero (`MvPolynomial.volume_setOf_eval_eq_zero`).
As far as I can tell, Mathlib has neither at the pinned version.

## Conventions

Lang writes $`g = kau`$ and so did my first project. Jorgenson and Lang write
$`g = uak`$. Inversion converts one into the other: if $`g = kau`$ then
$`g^{-1} = u^{-1} a^{-1} k^T`$ (`inv_iwasawa_jl`). The Cartan involution
$`\theta(g) = (g^T)^{-1}`$ does not do this. It fixes $`K`$, inverts $`A`$ and turns
upper unipotent matrices into lower unipotent ones. Jorgenson and Lang use it to
describe $`K`$ as its fixed points, and it's formalized here for that reason
(`cartanInvolution`, `cartanInvolution_involutive`).

Because of the order, the weight is $`\delta(a)`$ for $`kau`$ and $`\delta(a)^{-1}`$ for
$`uak`$. In Lie-theoretic notation $`\delta(a) = e^{2\rho(\log a)}`$.

## How the integration formula is proved

My original plan was a change of variables through the Jacobian above. That needs
an explicit Haar measure on $`K`$ in Cayley coordinates and a proof that it's left
invariant, which is what `IwasawaHaarK.lean` was building toward. It turned out not
to be necessary. The textbook proof (Knapp, Prop. 8.43; Folland, Thm. 2.51) only uses
uniqueness of Haar measure:

1. $`B = AU`$ is a group (upper triangular with positive diagonal), and
   $`(k, b) \mapsto k b^{-1}`$ identifies $`K \times B`$ with $`G`$.
2. Left multiplication by $`(k_0, b_0)`$ on $`K \times B`$ turns into
   $`g \mapsto k_0\, g\, b_0^{-1}`$ on $`G`$. Since $`G`$ is unimodular, Haar measure on
   $`G`$ is invariant under that, so its pullback is a left Haar measure on $`K \times B`$.
3. The measure $`dk\,\delta(a)\,da\,du`$, carried over to $`K \times B`$, is left invariant
   too. The reason is $`(au)(a'u') = (aa')\big((a'^{-1} u a')\, u'\big)`$: the
   $`A`$ coordinate gets translated, which costs a factor $`\delta(a')^{-1}`$, and the
   $`U`$ coordinate gets conjugated, which gives the $`\delta(a')`$ back.
4. Two left Haar measures on $`K \times B`$ agree up to a constant.

The Jacobian is still a good sanity check. In
$`2^{n(n-1)/2}(\det a)^n\,\delta(a)\,\det(1+X)^{-(n-1)}`$, the factor $`(\det a)^n`$ is
$`|\det g|^n`$, which the density $`|\det g|^{-n}`$ of Haar measure on
$`GL_n(\mathbb{R})`$ cancels, and $`2^{n(n-1)/2}\det(1+X)^{-(n-1)}`$ is the
Cayley-coordinate density of Haar measure on $`K`$. What's left is $`\delta(a)`$.

## Building

```sh
lake exe cache get   # prebuilt Mathlib
lake build
```

Lean `v4.30.0-rc1` and Mathlib commit `1708ec1f`, the same pin as the
Iwasawa_Decomposition repo. [BUILD.md](BUILD.md) has the details, including why
`project/Iwasawa.lean` is a vendored older copy of that repo's `Iwasawa.lean`.

`IwasawaIntegration.lean` ends with `#print axioms` for its main theorems wrapped in
`#guard_msgs`, so the build fails if any of them picks up a `sorry` or another
axiom. Five other files end with plain `#print axioms` blocks that show up in the
build output, and the eight `AxiomCheck*.lean` files, which aren't part of the default
build, hold 120 more. Run them with, for example,
`lake build iwasawa_change_of_coords.AxiomCheck`. CI runs `lake build` on pushes to
`main` and on pull requests.

## Where things are

| File | Contents |
| --- | --- |
| `project/Iwasawa.lean` | the decomposition $`g = kau`$ (vendored) |
| `IwasawaCoC.lean` | the four groups, bijection, homeomorphism, Lie decompositions, charts on $`G`$, $`U`$, $`A`$, the Cayley transform |
| `IwasawaSmoothK.lean` | the manifold structure on $`O(n)`$ |
| `MatrixContDiff.lean`, `IwasawaDiffeomorph.lean` | smoothness, the diffeomorphism |
| `IwasawaLieDecomposition.lean` | the Lie decomposition as `DirectSum.IsInternal`, and $`\mathrm{Sym}_n = \mathfrak{a} \oplus \mathfrak{n}_{\mathrm{sym}}`$ |
| `IwasawaMFDerivAtOne.lean`, `IwasawaMFDeriv.lean` | the derivative at the identity and at a general point |
| `IwasawaJacobianAbstract.lean`, `IwasawaJacobianExplicit.lean` | $`\det \mathrm{Ad}(a)\vert_{\mathfrak{n}} = \delta(a)`$ and the pieces of the Jacobian |
| `IwasawaComplete.lean` | the Jacobian determinant, Sylvester-Franke, clean restatements of the main results, the topological groups and their Haar measures |
| `IwasawaBridge.lean` | restatements of $`\det \mathrm{Ad}(a)\vert_{\mathfrak{n}} = \delta(a)`$ (this is where the old placeholder axiom used to be) |
| `IwasawaHaar.lean` | unimodularity of $`GL_n`$, the conjugation formula, explicit Haar measures |
| `IwasawaIntegration.lean` | the integration formula and the modular character of $`B`$ |
| `IwasawaHaarK.lean` | Haar measure on $`SO(n)`$ in Cayley coordinates (partial) |
| `PolynomialNullSet.lean` | zero sets of polynomials are null |

All of these except `project/Iwasawa.lean` are in `iwasawa_change_of_coords/`.
[docs/](docs) has longer write-ups: the math in [mathematics.md](docs/mathematics.md),
Lean signatures and a milestone index in [theorem-statements.md](docs/theorem-statements.md),
proof sketches in [proof-outlines.md](docs/proof-outlines.md), and some notes on what the
axiom checks do and don't certify in [methodology.md](docs/methodology.md). The other
markdown files in the root are my working notes from along the way. Some of them are
out of date, which the ones about the Haar measure say at the top.

## Notes on the formalization

- The Mathlib pin matters. For a while the build configuration pointed at the
  `v4.30.0-rc1` tag, 368 commits older than the Mathlib this was written against,
  and `IwasawaCoC.lean` failed there with `ChartedSpace` instances not found on the
  submodule model spaces. On the right commit the same file elaborates unchanged.
- The four groups are subtypes of `Matrix (Fin n) (Fin n) ℝ` with group instances
  written by hand, like in the first project. $`B = AU`$ is the one exception. It's a
  `Subgroup` of $`G`$, since it only exists to carry a Haar measure.
- The smooth part needs a normed ring structure on matrices, which Mathlib doesn't
  register globally, so the derivative files turn on the $`\ell^\infty`$ operator norm
  with local instances. The measure part avoids putting a measure on `Matrix`
  itself (its `MeasurableSpace` instance clashes with the one `volume` wants) and
  works on coordinate spaces like `nnIndex n → ℝ` instead.
- `PolynomialNullSet.lean` used to `import Mathlib`, which forces a build of all of
  Mathlib. It now imports the five modules it uses, and the whole project needs about
  2,500 Mathlib modules instead of about 7,900.

## What's not done

- The explicit Haar measure on $`K`$ in Cayley coordinates is incomplete.
  `nuK_eq_smul_haarK_of_invariant` reduces `nuK = c • haarK` to three facts about
  `nuK` that aren't proved yet: left invariance (the real work), finiteness on
  compacts, and inner regularity. The extension to the $`\det = -1`$ half of
  $`O(n)`$ is missing too. The change of variables for left invariance needs the
  Cayley chart domain after translating by $`k_0`$ to be co-null. That's proved
  whenever the domain is nonempty (`cayleyLeftDom_compl_null`), and nonemptiness is
  proved when $`1 + k_0`$ is invertible, but it's still open for $`k_0 \in SO(n)`$
  with eigenvalue $`-1`$ (`KDensityPlan.md`). The integration formula doesn't need
  any of this, but it would be a nice explicit description.
- The constant $`c`$ isn't computed. It depends on how the four Haar measures are
  normalized, and Mathlib's `Measure.haar` fixes those in a way that has nothing to
  do with this formula.
- Continuity of Gram-Schmidt and the polynomial null-set lemma would make reasonable
  Mathlib contributions.

## References

- J. Jorgenson and S. Lang, *Spherical Inversion on* $`SL_n(\mathbb{R})`$, Springer
  Monographs in Mathematics, 2001. Chapter I, §1 to §3.
- S. Lang, *Linear Algebra*, 3rd ed., Springer, 1987. Appendix II.
- A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002.
  Prop. 8.43.
- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press, 2016.
  Thm. 2.51.
- A. Cayley, "Sur quelques propriétés des déterminants gauches", *J. reine angew.
  Math.* 32 (1846), 119 to 123.
- Mathlib's `Mathlib/Geometry/Manifold/Instances/Sphere.lean` (Heather Macbeth), the
  model for the Cayley atlas.

## License

Released for educational and academic use.

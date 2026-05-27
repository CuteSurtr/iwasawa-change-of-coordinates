# Formula Reconciliation: Iwasawa Jacobian and Haar Measure

This file resolves the eight questions in the research brief by combining
sources from `00_bibliography.md` with a direct computation against the
existing Lean code in `IwasawaJacobianExplicit.lean` and `IwasawaMFDeriv.lean`.

All formulas use the conventions of the `IwasawaCoC` Lean project:

- `G = GL_n(R)`, `K = O(n)` (orthogonal), `A = positive diagonal`
  (raw matrices, not log coordinates at the group level), `N = UU =`
  upper unitriangular, `n = NN =` strict upper triangular Lie algebra.
- Iwasawa order: `g = k a u` with `k ∈ K`, `a ∈ A`, `u ∈ UU`.
- `nnIndex n = {(i, j) : Fin n × Fin n // i < j}`, cardinality `N := n(n-1)/2`.
- `iwasawaMatrixLeibnizCLM k a u` is the explicit Frechet derivative of
  the matrix-valued composition `Subtype.val ∘ iwasawaMap` at `(k, a, u)`.
- Source basis `iwasawaSourceBasis : Basis (Fin n × Fin n) R (Sk × (Fin n -> R) × NN)`.
  Within each pair {p, q} with p < q in lex order, source `(p, q)`
  (upper-side) comes before `(q, p)` (lower-side).
- Target basis `Matrix.stdBasis R (Fin n) (Fin n)`, indexed by
  `Fin n × Fin n` in lex order.
- `adNN a : NN -> NN` is `X -> a X a^{-1}`, diagonal in the
  pair-indexed basis `nnBasis` with eigenvalues `a_i / a_j` for `(i, j)`
  with `i < j`. Hence `LinearMap.det (adNN a) = ∏_{i<j} a_i / a_j`
  (theorem `adNN_det_eq_pair_product`).

## Q1: Standard Iwasawa Haar density factor for GL_n(R)

With the `KAN` ordering, the standard Haar decomposition is

```
∫_G f(g) dg = ∫_K ∫_A ∫_N f(k a u) · a^{2ρ} · dk · da · du
```

where

- `dk` is normalized Haar on `K = O(n)`,
- `da` is multiplicative Haar on `A = (R_{>0})^n`, i.e.
  `∏ da_i / a_i` in raw entries, or equivalently `∏ dH_i` in log
  coordinates `a = exp(H)`,
- `du` is additive Lebesgue on the n(n-1)/2 strict-upper-triangular
  entries of `u`,
- `a^{2ρ} = ∏_{i<j} a_i / a_j = det(Ad(a)|_n)`.

**Sources:** Knapp Proposition 8.43 and eq. 8.38; arXiv:1404.5535
eq. (24)-(26); Dowd §3.3 (GL_2 special case `dx dy/y^2 dθ`); Jana p. 3.

## Q2: Is the factor `∏_{i<j} a_i/a_j`, its inverse, or a det power?

It is the **positive-root product** `∏_{i<j} a_i/a_j` (NOT its inverse,
NOT a power of det(a)). Equivalently:

```
a^{2ρ} = ∏_{i<j} (a_i/a_j) = ∏_{i=1}^n a_i^{n - 2i + 1}     (1-indexed)
                            = ∏_{p=0}^{n-1} a_p^{n - 1 - 2p}  (0-indexed Lean)
```

`a^{-2ρ}` is the modular function `Δ_P` of the Borel `P = AN`
(Morel PS2). The two differ by reciprocal. The Knapp convention used
here puts `a^{+2ρ}` in the `KAN` integration formula.

**Sources:** Knapp eq. 8.38 (`det Ad_n(a) = e^{2ρ log a}`); Morel PS2
p. 5-6 (explicit `∏ a_i^{n-2i+1}` derivation); direct expansion shows
`∏_{i<j} a_i/a_j = ∏_i a_i^{n - 2i + 1}` by counting how many pairs
each `a_i` participates in.

## Q3: Relation to `det(adNN a)`

In the Lean project, `adNN a : NN ->L[R] NN` is conjugation by `a` on
the strict-upper-triangular Lie algebra. The theorem
`adNN_det_eq_pair_product` states

```
LinearMap.det (adNN a).toLinearMap = ∏ ij : nnIndex n, a_{ij.1.1} / a_{ij.1.2}
                                    = ∏_{i<j} a_i / a_j
```

This is **identical** to the `a^{2ρ}` factor of Q2. So

```
det(adNN a) = a^{2ρ} = ∏_{i<j} a_i/a_j = ∏_i a_i^{n - 2i + 1} (1-idx).
```

## Q4: Why the ambient Lebesgue Jacobian has an extra `det(a)^n`

The ambient matrix Lebesgue measure on `M_n(R)` is NOT the Haar measure
of `GL_n(R)`. The Haar measure is

```
dg_Haar = |det g|^{-n} dM    (Q5 below).
```

The map `iwasawaMap : K × A × N -> G` evaluated through chart
coordinates `(X, H, Z) ∈ (Sk × R^n × NN)` (with `K` via Cayley chart,
`A` via log coordinates, `N` via identity) has derivative

```
iwasawaMatrixLeibnizCLM k a u : Sk × R^n × NN ->L[R] M_n(R)
```

into AMBIENT matrix space (M_n(R) with its Lebesgue measure
`dM = ∏ dg_{ij}`).

A direct entry-by-entry computation (next paragraph) shows that at
`(k = 1, a, u = 1)`, the Lebesgue Jacobian in these chart coordinates is

```
|det iwasawaMatrixLeibnizCLM 1 a 1| = 2^N · det(a)^n · det(adNN a)
                                    = 2^N · det(a)^n · ∏_{i<j} a_i/a_j
```

where `N = n(n - 1)/2`. The `det(a)^n` factor appears because the
ambient Lebesgue is M_n(R)-Lebesgue, NOT Haar on GL_n(R). It is
precisely the factor that gets cancelled when one converts from
M_n(R)-Lebesgue to Haar via `dg_Haar = |det g|^{-n} dM` (Q6).

**The block-determinant computation.** For pair `{p, q}` with `p < q`,
inspection of the entry lemmas
`iwasawaMatrixLeibnizCLM_one_a_one_source_*_*_entry` in
[IwasawaJacobianExplicit.lean](../../IwasawaJacobianExplicit.lean) gives:

- source `(p, q)` (upper of pair): only nonzero target entry is `(p, q) = a_pp`;
- source `(q, p)` (lower of pair): nonzero target entries are
  `(p, q) = -2 a_qq` and `(q, p) = +2 a_pp`;
- source `(i, i)` (diagonal): only nonzero target entry is `(i, i) = a_ii`.

So in the source/target block indexed by `[(p, q), (q, p)]` for both
rows and columns (lex order: `(p, q)` comes first since `p < q`), the
2x2 block is

```
                col (p, q) upper    col (q, p) lower
row (p, q)            a_pp                -2 a_qq
row (q, p)            0                    2 a_pp
```

with determinant `+ 2 · a_pp^2`. There are `N` such 2x2 blocks, one per
pair, all sharing the same `+2` sign. The diagonal blocks contribute
`∏_i a_ii = det(a)`. By the standard block-diagonal identity
(invariance of det under simultaneous row+column permutation), the
total determinant is

```
det = (∏_{p < q} 2 a_pp^2) · det(a)
    = 2^N · (∏_{p < q} a_pp^2) · det(a)
    = 2^N · (∏_p a_p^{2(n - 1 - p)}) · det(a)        (counting q > p)
    = 2^N · (∏_p a_p^{2(n - 1 - p) + 1})
    = 2^N · (∏_p a_p^{2n - 1 - 2p})
    = 2^N · (∏_p a_p^n) · (∏_p a_p^{n - 1 - 2p})
    = 2^N · det(a)^n · det(adNN a).
```

**The sign is `+2^N`, not `(-2)^N`.** See the "Convention Risks" section
below.

## Q5: Haar on GL_n(R) versus ambient matrix Lebesgue

Haar on `GL_n(R)` is

```
dg_Haar = |det g|^{-n} dM
```

where `dM = ∏_{i, j} dg_{ij}` is the ambient Lebesgue restricted to the
open set `GL_n(R) ⊂ M_n(R)`. The exponent is exactly `-n`, NOT `-n+1`
or `-n^2`.

Sketch: left translation `L_g : M_n(R) -> M_n(R), M -> g · M` is a
linear endomorphism on R^{n^2}. Its matrix (in any standard basis) is
block-diagonal with `n` copies of `g` (one per column of M). Hence
det L_g = (det g)^n, so dM scales by `|det g|^n` under L_g. Dividing
by `|det M|^n` gives an L_g-invariant measure; the same argument on the
right shows GL_n(R) is unimodular.

**Sources:** Wikipedia "Haar measure"; Dowd §3.1; Olafsson Example 1;
Lei §1.4 via Goldfeld. All agree on the exponent `-n`.

## Q6: Cancellation of `det(a)^n` in the Iwasawa coordinates

Under `g = k a u`:

```
|det g| = |det k| · |det a| · |det u| = 1 · det(a) · 1 = det(a)
```

(since `a` has positive diagonal). Substituting into the Haar formula:

```
dg_Haar = |det g|^{-n} dM
        = det(a)^{-n} dM
        = det(a)^{-n} · |det iwasawaMatrixLeibnizCLM 1 a 1| · dchart(K) dchart(A) dchart(N)
        = det(a)^{-n} · 2^N · det(a)^n · det(adNN a) · dchart(K) dchart(A) dchart(N)
        = 2^N · det(adNN a) · dchart(K) · dchart(A) · dchart(N).
```

So the `det(a)^n` factor from the ambient Lebesgue Jacobian is exactly
absorbed by `|det g|^{-n} = det(a)^{-n}` in the Haar density.

After cancellation, the chart-coordinate Haar density is

```
dg_Haar = 2^N · det(adNN a) · dchart(K) · dchart(A) · dchart(N).
```

The `2^N` is a chart artifact from the Cayley parametrization of `K`
(the chart's derivative at the identity is `-2 X` for `X ∈ Sk`); a
different chart on `K` would replace `2^N` with a different constant.
The intrinsic factor is `det(adNN a) = a^{2ρ}`, matching Knapp's
formula `dg = a^{2ρ} dk da dn`.

## Q7: Final expected relationships

- **Ambient matrix Jacobian** (Lebesgue on M_n(R) restricted to GL_n(R)):

  ```
  |det iwasawaMatrixLeibnizCLM 1 a 1| = 2^N · det(a)^n · det(adNN a).
  ```

  At general `(k, a, u)` this becomes
  `|det iwasawaMatrixLeibnizCLM k a u| = 2^N · det(a)^n · det(adNN a)`,
  because left translation by k and right multiplication by u in the
  ambient matrix space are linear isometries (k orthogonal, u
  unipotent) of M_n(R) with determinant ±1 on M_n(R). See "Open
  Questions" for verification.

- **Haar Iwasawa density** (after dividing by `|det g|^n = det(a)^n`):

  ```
  dg_Haar = (chart constants) · det(adNN a) · dk_chart · da_chart · du_chart.
  ```

  The chart constants depend on the K chart (`2^N` here) and on whether
  `da` is multiplicative Haar on A or Lebesgue in log coordinates.

## Q8: Convention risks (READ CAREFULLY)

1. **Sign of the prefactor.** The research brief tentatively
   expected `(-2)^N`. The actual sign from the basis ordering in
   `iwasawaSourceBasis` is `+2^N`. The negative sign would appear only
   if rows and columns within each pair were ordered differently, which
   does NOT happen in the Lean code's lex-ordered basis. **Use `+2^N`.**

2. **KAN versus NAK ordering.** Knapp gives both:
   `dx = a^{2ρ} dk da dn` (KAN) vs `dx = da dn dk` (ANK, no factor).
   The project uses KAN, so `a^{2ρ}` appears.

3. **`a^{2ρ}` vs `a^{-2ρ}` (Δ_P vs det Ad_n).** Bourbaki-style modular
   function `Δ_P(p) = a^{-2ρ}` is the reciprocal of Knapp's
   `det Ad_n(a) = a^{+2ρ}`. The Lean `adNN_det_eq_pair_product` gives
   `+2ρ` (the determinant of conjugation), matching Knapp. The
   distinction matters when reading Borel/parabolic literature: check
   whether the source means `Δ_P` (Haar-character-of-Borel) or
   `det Ad_n` (eigenvalue product).

4. **log coordinates vs raw multiplicative on A.** Knapp's `da` is
   Haar on A, which equals `∏ da_i / a_i` in raw entries OR `∏ dH_i` in
   log coordinates. The Lean source basis for A uses `Fin n -> R`,
   which is the LIE ALGEBRA (log coordinates). So `da_chart = ∏ dH_i =
   da_Haar`. NO extra `1/det(a)` factor needed for this chart choice.

5. **Upper vs lower unitriangular N.** Project uses upper.
   `det(adNN a) = ∏_{i<j} a_i/a_j > 0` for `a_i > 0` and `i < j`. If
   someone uses lower unitriangular N (with strictly lower as `n`),
   the eigenvalues invert to `a_j/a_i` for `i < j`, giving the
   reciprocal. The current Lean convention is upper.

6. **K chart with -2 factor.** The Cayley chart `c : Sk -> K`,
   `c(X) = (I - X)(I + X)^{-1}`, satisfies `dc_0(X) = -2 X` (well known;
   derivative of Cayley at the origin). This is where the `2^N`
   prefactor in the ambient Jacobian comes from. A chart with derivative
   `+X` (e.g., a partial-exp) would give `1^N = 1`. The choice of chart
   is documented in the IwasawaMFDeriv.lean header.

7. **Mathlib's `addHaar` normalization.** `Basis.addHaar` normalizes the
   parallelepiped of the basis to measure 1. So the precise multiplicative
   constant of `dchart(K)`, `dchart(A)`, `dchart(N)` depends on which basis
   we use for `addHaar`. The `2^N` factor in Q7 is correct for the
   `iwasawaSourceBasis`-normalized Lebesgue on the source space.

8. **Helgason vs Knapp ρ convention.** Helgason often uses `ρ` = full
   sum of positive roots (no factor of 1/2); Knapp uses `2ρ` for that
   sum. Both arrive at the same `a^{2ρ}` factor; just be careful when
   transcribing.

9. **Modular character on GL_n(R).** GL_n(R) is unimodular, so the
   modular character `Δ_G ≡ 1`. The non-trivial modular character is
   for the BOREL `P = AN`, which is non-unimodular. Mathlib's
   `Measure.modularCharacter` would be trivially 1 for GL_n(R) and
   would not give the Iwasawa formula directly.

10. **QR Jacobian power: `n - i`, not `i - 1`.** Edelman-Rao eq. (3.6)
    for real square: `∏_{i=1}^n r_ii^{n - i}`. Wikipedia Wishart confirms
    via Bartlett `c_i^2 ~ χ^2_{n - i + 1}`. The opposite power `i - 1`
    would correspond to a reversed-indexing convention (lower-triangular
    Cholesky or reversed Iwasawa). Stick with `n - i` for upper R.

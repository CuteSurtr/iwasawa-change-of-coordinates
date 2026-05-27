# One-Page GPT Summary: Iwasawa Jacobian and Haar for `IwasawaCoC`

(A dense page meant to replace re-reading all source PDFs and source
files. Read this before starting Stage 4B2.)

## Setup

- Group: `G = GL_n(R)` (Lean: `G n`, open subset of `M_n(R)`).
- Iwasawa decomposition: `g = k a u`, with `K = O(n)`, `A = positive
  diagonal`, `U = upper unitriangular` (Lean: `K n, A n, UU n`).
- Lie algebras: `Sk n` (skew-sym, = Lie K), `Fin n → R` (= Lie A, via
  log coordinates on A), `NN n` (strict upper triangular, = Lie U).
- Index: `nnIndex n = {(i, j) : Fin n × Fin n // i < j}`,
  cardinality `N := n(n-1)/2`.

## The three intrinsic formulas

1. **Pair-product (already proved):**
   `LinearMap.det (adNN a) = ∏_{i < j} a_i / a_j = ∏_p a_p^{n - 1 - 2p}` (Lean 0-indexed).
   Theorem `adNN_det_eq_pair_product`.

2. **Ambient matrix Lebesgue Jacobian of the Iwasawa map** at `(1, a, 1)`:
   `detInIwasawaBases (iwasawaMatrixLeibnizCLM 1 a 1) = 2^N · det(a)^n · det(adNN a)`.
   (Sign is `+`, NOT `(-2)^N`. Derived by 2x2 block-determinant
   computation per pair {p, q} with p < q: block det = `+ 2 a_pp^2`.)

3. **Haar on GL_n(R) versus ambient Lebesgue:**
   `dg_Haar = |det g|^{-n} dM`, where `dM = ∏ dg_{ij}`. Exponent is `-n`.

Combining (2) and (3) gives the Iwasawa Haar formula in chart
coordinates: `dg_Haar = 2^N · det(adNN a) · dk_chart · da_chart · du_chart`.
The `2^N` is a Cayley-chart artifact (the Cayley parametrization of K
has derivative `-2 X` at I); a different K chart replaces `2^N` with a
different constant. The intrinsic factor is `det(adNN a) = a^{2ρ}`,
matching Knapp Proposition 8.43.

## Block-determinant computation (the key new fact)

At `(k = 1, a, u = 1)`, the source basis is `iwasawaSourceBasis`
indexed by `Fin n × Fin n` (lex), target is `Matrix.stdBasis` indexed
by `Fin n × Fin n` (lex). Entry lemmas already in
`IwasawaJacobianExplicit.lean`:

```
src (i, i):   target (i, i) = a_ii.                    [diag]
src (p, q), p < q (upper): target (p, q) = a_pp.        [upper col]
src (q, p), p < q (lower): target (q, p) = 2 a_pp,
                           target (p, q) = -2 a_qq.    [lower col]
all other entries are zero.
```

Per pair {p, q} (p < q), the 2x2 block in basis
`[src (p, q), src (q, p)] × [tgt (p, q), tgt (q, p)]` is

```
[ a_pp     -2 a_qq ]
[ 0         2 a_pp ]
```

with det `+2 a_pp^2`. Diagonal: `n` blocks contributing `a_ii`.
Cross-block entries are zero. By simultaneous row+column permutation
to block-diagonal form, total det is

```
(∏_i a_ii) · ∏_{p<q} 2 a_pp^2 = det(a) · 2^N · ∏_p a_p^{2(n-1-p)}
                              = 2^N · det(a)^n · det(adNN a).
```

## Lean target theorems (Stage 4B2 to 4B3)

```lean
-- Stage 4B2: normalized signed formula.
theorem detInIwasawaBases_one_a_one_eq (a : A n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM ⟨1, .one⟩ a ⟨1, .one⟩) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap

-- Trivial corollary (a positive, adNN a det positive).
theorem absDetInIwasawaBases_one_a_one_eq (a : A n) :
    absDetInIwasawaBases (...) = same RHS

-- Stage 4B3: general (k, a, u).
theorem absDetInIwasawaBases_general_eq (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) = same RHS
```

## Mathlib APIs to call

- Linear algebra:
  - `LinearMap.det_toMatrix` (already used by `adNN_det_eq_pair_product`).
  - `Matrix.det_diagonal`, `Matrix.det_fromBlocks_zero₂₁` (for the 2x2
    block).
  - `Basis.reindex` (does NOT change `LinearMap.det`).
  - `Finset.prod_*` lemmas for the exponent rearrangement.

- Measure theory (later stages):
  - `Basis.addHaar`, `Basis.prod_addHaar` (reference Lebesgue on
    chart space).
  - `integral_image_eq_integral_abs_det_fderiv_smul`,
    `lintegral_abs_det_fderiv_eq_addHaar_image`,
    `map_withDensity_abs_det_fderiv_eq_addHaar`
    (change of variables; in `MeasureTheory.Function.Jacobian`).
  - `haarMeasure_unique`, `IsMulLeftInvariant` (for identifying
    pushforward with abstract Haar).

NOT needed for the main route:
- `Measure.modularCharacter` (GL_n(R) is unimodular).
- `MeasureTheory.Measure.Haar.MulEquivHaarChar`,
  `MeasureTheory.Measure.Haar.DistribChar` (intrinsic but not needed
  for the explicit chart formula).

## Source citations (one-line)

- Knapp, Lie Groups Beyond an Introduction (Stony Brook PDF):
  Proposition 8.43 = `dx = a^{2ρ} dk da dn` (KAN order).
- Mezzadri, arXiv:math-ph/0609050: QR with positive diagonal, Haar
  invariance.
- Edelman-Rao, Acta Numerica 2005 (math.mit.edu PDF):
  `dA = ∏ r_ii^{n-i} dR (Q^T dQ)` for real square QR.
- Dowd (math.berkeley.edu PDF): `GL_n` Haar = `|det h|^{-n} dM`.
- Olafsson Ch. 6 (math.lsu.edu PDF): independent derivation of
  `|det X|^{-n}` Haar on GL_n(R).
- Morel MAT 449 PS2 (math.princeton.edu PDF): explicit
  `det(c_a) = ∏ a_i^{n-2i+1}` matching the pair-product.

## Convention risks to track

1. Sign is `+2^N`, not `(-2)^N`. Direct from lex basis ordering.
2. KAN order is what the project uses; matches Knapp Prop 8.43.
3. `det(adNN a) = a^{+2ρ}`, NOT `a^{-2ρ} = Δ_P(a)`. Bourbaki conventions
   may differ.
4. log coordinates on A: `da_chart` is already Haar on A (no extra
   `1/det(a)` factor in this chart).
5. Cayley chart on K introduces the `2^N` factor.
6. Mathlib `addHaar` normalizes the basis-parallelepiped to mass 1.

## Recommended next prompt (copy-paste below)

(See `END OF FILE: recommended next prompt for Lean implementation`
in this packet.)

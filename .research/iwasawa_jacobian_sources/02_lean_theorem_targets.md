# Lean Theorem Targets for Stage 4B2

This file proposes concrete Lean theorem signatures for the next stage
of the `IwasawaCoC` project, building on
[`IwasawaJacobianExplicit.lean`](../../IwasawaJacobianExplicit.lean).

## Existing objects (already in the project)

```lean
-- Actual derivative of the matrix-valued Iwasawa composition.
-- File: IwasawaMFDeriv.lean.
noncomputable def iwasawaMatrixLeibnizCLM
    (k : K n) (a : A n) (u : UU n) :
    (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ] Matrix (Fin n) (Fin n) ℝ

-- Bases.
noncomputable def skBasis : Basis (nnIndex n) ℝ (Sk n)
noncomputable def nnBasis : Basis (nnIndex n) ℝ (NN n)
noncomputable def iwasawaSourceBasisProd :
    Basis ((nnIndex n) ⊕ ((Fin n) ⊕ (nnIndex n))) ℝ
      ((Sk n) × ((Fin n → ℝ) × (NN n))) :=
  skBasis.prod ((Pi.basisFun ℝ (Fin n)).prod nnBasis)
noncomputable def iwasawaSourceBasis :
    Basis (Fin n × Fin n) ℝ ((Sk n) × ((Fin n → ℝ) × (NN n))) :=
  iwasawaSourceBasisProd.reindex (iwasawaSourceIndexEquiv (n := n))

-- Determinant helpers.
noncomputable def detInIwasawaBases
    (L : (Sk n) × ((Fin n → ℝ) × (NN n)) →L[ℝ] Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (LinearMap.toMatrix iwasawaSourceBasis (Matrix.stdBasis ℝ (Fin n) (Fin n))
    L.toLinearMap).det

noncomputable def absDetInIwasawaBases (L : ...) : ℝ := |detInIwasawaBases L|

-- Existing nonvanishing theorem (already proved at normalized k, u = 1).
theorem detInIwasawaBases_one_a_one_ne_zero (a : A n) :
  detInIwasawaBases (iwasawaMatrixLeibnizCLM ⟨1, .one⟩ a ⟨1, .one⟩) ≠ 0

-- Eigenvalue product on the unipotent Lie algebra.
theorem adNN_det_eq_pair_product (a : A n) :
  LinearMap.det (adNN a).toLinearMap =
    ∏ ij : nnIndex n, a.1 ij.1.1 ij.1.1 / a.1 ij.1.2 ij.1.2
```

## Proposed next theorem: normalized signed formula

```lean
/-- Stage 4B2 main: the signed determinant of the actual derivative of
`iwasawaMap` at the normalized point `(1, a, 1)`, expressed in the
`iwasawaSourceBasis` and `Matrix.stdBasis`. -/
theorem detInIwasawaBases_one_a_one_eq (a : A n) :
    detInIwasawaBases
      (iwasawaMatrixLeibnizCLM
        ⟨1, IsOrthogonal.one⟩ a ⟨1, IsUpperUnipotent.one⟩) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap
```

**Sign note.** The research brief tentatively wrote `(-2)^N`. A direct
entry-by-entry block-determinant computation gives `+ (2 : ℝ) ^ N`
under the lex ordering of `iwasawaSourceBasis` and `Matrix.stdBasis`.
See `01_formula_reconciliation.md` Q4 for the derivation. The 2x2 block
determinant for each pair `{p, q}` with `p < q` is

```
det [ a_pp     -2 a_qq ]  =  2 a_pp^2 .
    [ 0         2 a_pp ]
```

If a later proof finds that the sign comes out negative, it means the
basis ordering within each pair (lex vs reverse-lex) is opposite to
what is currently in `iwasawaSourceIndexEquiv`. The CURRENT Lean code's
lex order gives `+`.

## Proposed absolute determinant formula

```lean
/-- Stage 4B2 absolute determinant: ready for `MeasureTheory.Function.Jacobian`. -/
theorem absDetInIwasawaBases_one_a_one_eq (a : A n) :
    absDetInIwasawaBases
      (iwasawaMatrixLeibnizCLM
        ⟨1, IsOrthogonal.one⟩ a ⟨1, IsUpperUnipotent.one⟩) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap
```

(Same RHS; no absolute values needed on the RHS because `a.1.det > 0`
and `LinearMap.det (adNN a) > 0` by Q below.)

## Why `a.1.det` is positive and absolute values can be simplified

- `a : A n` is `{D | IsPositiveDiagonal D}` (see IwasawaCoC.lean:64). The
  property `IsPositiveDiagonal D` says `D` is diagonal with all
  diagonal entries `> 0`. Hence `D.det = ∏_i D_ii > 0`.
- `LinearMap.det (adNN a) = ∏_{i<j} a_i/a_j > 0` (each factor positive).
- The constant `(2 : ℝ) ^ N > 0`.

So `|...| = ...` on the RHS, and the absolute and signed determinant
formulas have the same RHS.

In Lean:

```lean
lemma posDiag_det_pos (a : A n) : 0 < a.1.det := by
  simp only [Matrix.det_diagonal]  -- or via det of diagonal matrix
  exact Finset.prod_pos (fun i _ => a.2.2 i)
```

Then

```lean
lemma absDetInIwasawaBases_one_a_one_eq' (a : A n) :
    absDetInIwasawaBases
      (iwasawaMatrixLeibnizCLM ⟨1, .one⟩ a ⟨1, .one⟩) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap := by
  rw [absDetInIwasawaBases_def, detInIwasawaBases_one_a_one_eq]
  rw [abs_of_pos]
  · rfl
  · positivity_or_explicit_proof
```

## Fallback theorems (use if exact signs are painful)

If the signed formula proof gets stuck on permutation-sign bookkeeping,
weaker theorems still close the chart-level change-of-variables story:

### Fallback A: nonvanishing constant

```lean
theorem detInIwasawaBases_one_a_one_eq_const_mul_product (a : A n) :
    ∃ c : ℝ, c ≠ 0 ∧
      detInIwasawaBases
        (iwasawaMatrixLeibnizCLM ⟨1, .one⟩ a ⟨1, .one⟩) =
      c * (a.1.det) ^ n * LinearMap.det (adNN a).toLinearMap
```

`c = 2^N` is the target, but a weaker existence form suffices for many
downstream chart-pushforward arguments where only the `a`-dependence
matters.

### Fallback B: ratio is independent of a

```lean
theorem detInIwasawaBases_ratio_const (a : A n) :
    detInIwasawaBases
      (iwasawaMatrixLeibnizCLM ⟨1, .one⟩ a ⟨1, .one⟩) /
        ((a.1.det) ^ n * LinearMap.det (adNN a).toLinearMap) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
```

(requires denominator nonzero, which follows from positivity).

### Fallback C: already proved nonvanishing

```lean
detInIwasawaBases_one_a_one_ne_zero : already in IwasawaJacobianExplicit.lean
```

Sufficient as input to invoke `MeasureTheory.Function.Jacobian` if the
explicit formula is not yet needed.

## Generalization beyond `(1, a, 1)`

The map `iwasawaMap : K × A × UU -> G` has derivative at general
`(k, a, u)` related to the normalized derivative by left translation
on the target and a change of basis on the source. Specifically, for
the matrix-valued composition `Subtype.val ∘ iwasawaMap`, left
multiplication by `k` is an isometry of `M_n(R)` with `|det L_k| = 1`
(orthogonal), and right multiplication by `u` is unipotent of det 1.
Heuristically:

```
|det (mfderiv at (k, a, u))| = |det L_k|^{nope}... no, this is not quite right
```

The correct statement is: the actual derivative at `(k, a, u)` factors
through a multiplication-by-k-on-the-left-and-u-on-the-right structure
that preserves Lebesgue volume on M_n(R), so

```
theorem absDetInIwasawaBases_general_eq (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap
```

is the target. This requires showing that left translation `M -> k * M`
on M_n(R) has `|det| = 1` for `k ∈ O(n)`, and that right translation
`M -> M * u` for `u` upper unitriangular has `|det| = 1`. Both reduce
to standard determinant facts (`det L_k = (det k)^n = (±1)^n = ±1` and
`det R_u = (det u)^n = 1`).

## Which theorem to feed into `MeasureTheory.Function.Jacobian`

The Jacobian lemmas `integral_image_eq_integral_abs_det_fderiv_smul`
and `lintegral_abs_det_fderiv_eq_addHaar_image` take the ABSOLUTE
value of the determinant of the Fréchet derivative.

The most useful form for these lemmas is

```lean
absDetInIwasawaBases_general_eq : ... =
  (2 : ℝ) ^ N * (a.1.det) ^ n * LinearMap.det (adNN a).toLinearMap
```

(combined with the bridge lemma from `MathlibInfrastructureMap.md` §2:
relate `detInIwasawaBases` to `(mfderiv iwasawaMap (k, a, u)).det` via
the chart's identity differential on the open subset
`G n ⊂ M_n(R)`).

If only the nonvanishing (fallback C) is available, you can still
state Jacobian-style change-of-variables BUT the resulting density is
left as an abstract function. The explicit formula `2^N · det(a)^n ·
det(adNN a)` is what turns the abstract change-of-variables into a
quotable Haar formula.

## Recommended ordering of theorem targets

1. `detInIwasawaBases_one_a_one_eq` (normalized signed formula). Hardest;
   yields the cleanest downstream form.
2. `absDetInIwasawaBases_one_a_one_eq` (trivial corollary via Q on
   positivity).
3. `absDetInIwasawaBases_general_eq` (k, a, u variant; uses left/right
   translation isometry arguments).
4. Then bridge to `mfderiv` and chart-level change of variables.
5. Then Haar.

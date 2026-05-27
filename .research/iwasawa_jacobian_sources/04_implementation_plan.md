# Implementation Plan: Jacobian and Haar for `IwasawaCoC`

## Current state (entering Stage 4B2)

- Actual derivative: `iwasawaMatrixLeibnizCLM k a u` (in
  `IwasawaMFDeriv.lean`).
- Source basis: `iwasawaSourceBasis : Basis (Fin n × Fin n) ℝ ...`
  (in `IwasawaJacobianExplicit.lean`).
- Source basis is reindexed from `iwasawaSourceBasisProd` (a sum-typed
  `skBasis ⊕ (Pi.basisFun ⊕ nnBasis)`).
- Target basis: `Matrix.stdBasis ℝ (Fin n) (Fin n)`.
- Det shells: `detInIwasawaBases`, `absDetInIwasawaBases`.
- Already proved: `detInIwasawaBases_one_a_one_ne_zero`,
  `adNN_det_eq_pair_product`.
- Entry-level lemmas at `(1, a, 1)`: `..._source_lower_lower_entry`,
  `..._source_lower_upper_entry`, `..._source_upper_upper_entry`,
  `..._source_diag_diag_entry`, plus the `toMatrix`-wrapped versions
  `..._toMatrix_*_*_entry`.

## Phase 0 (Stage 4B2): explicit normalized determinant formula

Goal:
```lean
theorem detInIwasawaBases_one_a_one_eq (a : A n) :
    detInIwasawaBases (iwasawaMatrixLeibnizCLM
      ⟨1, IsOrthogonal.one⟩ a ⟨1, IsUpperUnipotent.one⟩) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap
```

### Step 0.1: choose a basis arrangement that makes the determinant
straightforward

Two options:

(a) Stay with `iwasawaSourceBasis` (lex-ordered by `Fin n × Fin n`),
prove block-diagonal structure after permutation, and apply
`Matrix.det_blockDiagonal` (or simultaneous row+column permutation +
`Matrix.det_blockDiagonal`).

(b) Define a NEW basis ordered by "pair-blocks": list all diagonal
indices first, then for each pair `{p, q}` with `p < q` list the two
basis vectors consecutively. With this ordering, the matrix is
block-diagonal IN THE RAW SENSE (no permutation needed), and
`Matrix.det_blockDiagonal` applies directly. The new basis is related
to `iwasawaSourceBasis` by a reindex (an explicit `Equiv (Fin n × Fin n) _`).
`Basis.reindex` does NOT change `LinearMap.det` (this is a key
mathlib lemma, see below), so `detInIwasawaBases` is unchanged.

**Recommendation: (b)**. Define

```lean
def iwasawaBlockIndex (n : ℕ) : Type :=
  (Fin n) ⊕ (nnIndex n × Bool)
-- inl i: diagonal position (i, i)
-- inr (ij, false): upper-side source for pair ij (= (ij.1.1, ij.1.2))
-- inr (ij, true):  lower-side source for pair ij (= (ij.1.2, ij.1.1))

def iwasawaBlockIndexEquiv : iwasawaBlockIndex n ≃ Fin n × Fin n where
  ...

noncomputable def iwasawaBlockBasis :
    Basis (iwasawaBlockIndex n) ℝ ((Sk n) × ((Fin n → ℝ) × (NN n))) :=
  iwasawaSourceBasis.reindex iwasawaBlockIndexEquiv.symm
```

Then prove via `Basis.det_reindex` (mathlib) that the determinant in
this basis equals the original `detInIwasawaBases`.

Alternative: skip the block-basis trick and directly compute the
6-character-class permutation sign by hand. More painful.

### Step 0.2: assemble the matrix and identify the block structure

For each diagonal index `i`, the column has a single nonzero entry at
row `(i, i)`, value `a_ii`. So the `n × n` diagonal block of the matrix
is `Matrix.diagonal (fun i => a_ii) = Matrix.diagonal a.1.diag`.

For each pair index `ij : nnIndex n` (i.e., `(p, q)` with `p < q`), the
two columns are source upper `(p, q)` and source lower `(q, p)`. The two
nonzero target rows are `(p, q)` and `(q, p)`. The 2x2 block (rows in
the order [(p, q), (q, p)] and columns in the same order) is

```
[ a_pp     -2 a_qq ]
[ 0         2 a_pp ]
```

Cross-block entries are all zero: the entry lemmas
`iwasawaMatrixLeibnizCLM_one_a_one_source_*_entry` show that the image
of a "pair-block" source basis vector has support contained in the same
"pair-block" target rows.

### Step 0.3: assemble the determinant

```lean
-- One pair-block determinant.
have block_det : ∀ (p q : Fin n) (hpq : p < q),
    2x2_det_of_pair p q hpq = 2 * (a.1 p p) ^ 2 := by ...

-- Diagonal block determinant.
have diag_det : ... = ∏ i, a.1 i i = a.1.det := by
  simp [Matrix.det_diagonal]   -- via Iwasawa.IsPositiveDiagonal.det

-- Combine.
have total : detInIwasawaBases ... =
    a.1.det * ∏ ij : nnIndex n, 2 * (a.1 ij.1.1 ij.1.1) ^ 2 := ...

-- Rearrange to match the target form.
have rearrange :
    a.1.det * ∏ ij : nnIndex n, 2 * (a.1 ij.1.1 ij.1.1) ^ 2 =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, ...]
  rw [adNN_det_eq_pair_product]
  -- Exponent matching: ∏ a_p^{2(n-1-p)} * det(a) = det(a)^n * ∏ a_p^{n-1-2p}
  -- via a^{n} = a^{1} * a^{n-1} per index, etc.
  ring_or_field_simp_attack
```

Key supporting mathlib lemma:
- `Finset.prod_mul_distrib`
- `Finset.prod_const`
- `Matrix.det_diagonal`
- `Matrix.det_fromBlocks_zero₂₁` (for one 2x2 block):
  `det [A B; 0 D] = det A * det D` (with the bottom-left being zero).

### Step 0.4: connect to `adNN_det_eq_pair_product`

The product `∏_{p < q} 2 a_pp^2` rearranges to
`2^N · ∏_p a_p^{2(n-1-p)}` (count pairs containing index p).

The product `det(a)^n · det(adNN a) = ∏_p a_p^n · ∏_{i<j} a_i/a_j`
expands using `adNN_det_eq_pair_product`:

```
∏_p a_p^n · ∏_{i<j} a_i/a_j = ∏_p a_p^n · ∏_p a_p^{n-1-2p}
                            = ∏_p a_p^{n + n - 1 - 2p}
                            = ∏_p a_p^{2n - 1 - 2p}
                            = ∏_p a_p^{2(n-1-p) + 1}
                            = ∏_p a_p · ∏_p a_p^{2(n-1-p)}
                            = det(a) · ∏_p a_p^{2(n-1-p)}.
```

So `det(a)^n · det(adNN a) = det(a) · ∏_p a_p^{2(n-1-p)}`, and the
goal becomes a pure `Finset.prod` rearrangement.

Tactics: `Finset.prod_mul_distrib`, `Finset.prod_pow`,
`Finset.prod_const`, `Finset.prod_comm`, possibly `Fin.prod_univ_succ`
for inductive unfolding if needed. Or `ring_nf` after sufficient
`simp`-rewrites.

---

## Phase 1 (Stage 4B3): absolute determinant at general `(k, a, u)`

Goal:
```lean
theorem absDetInIwasawaBases_general_eq (k : K n) (a : A n) (u : UU n) :
    absDetInIwasawaBases (iwasawaMatrixLeibnizCLM k a u) =
      (2 : ℝ) ^ Fintype.card (nnIndex n)
        * (a.1.det) ^ n
        * LinearMap.det (adNN a).toLinearMap
```

Strategy:
- Express `iwasawaMatrixLeibnizCLM k a u` as the composition
  `L_k ∘ (iwasawaMatrixLeibnizCLM 1 a 1) ∘ ... ∘ R_u`-style maneuver,
  where left and right translations have `|det| = 1`.
- Concretely, the Leibniz expansion of the derivative of `(k, a, u) →
  k * a * u` is `dk · a · u + k · da · u + k · a · du`, plus the
  Cayley-chart `-2` factor on the K direction. At the matrix level,
  this assembles into `iwasawaMatrixLeibnizCLM k a u = L_k_matrix ∘
  (iwasawaMatrixLeibnizCLM 1 a 1) ∘ <change-of-source-basis>` perhaps
  composed with `R_u_matrix`.
- `det L_k = (det k)^n = ±1` (orthogonal); `det R_u = (det u)^n = 1`
  (unipotent).
- Taking absolute values, the `±1` factors disappear and the formula
  matches the normalized case.

Alternative simpler route:
- Prove directly the entry-by-entry formulas at general `(k, a, u)` and
  redo the block determinant. Less elegant but mechanical.

---

## Phase 2 (Stage 4C): bridge to `mfderiv`

The differential of `iwasawaMap` as a smooth map between manifolds is
`mfderiv 𝓘 𝓘 iwasawaMap`. Existing infrastructure
(`MathlibInfrastructureMap.md` §1, and `IwasawaMFDeriv.lean`) connects
this to `iwasawaMatrixLeibnizCLM` via:

```lean
theorem mfderiv_iwasawaMap_at_factored ...
```

(already in the codebase). This lets us replace
`mfderiv iwasawaMap` by `iwasawaMatrixLeibnizCLM` in any
chart-coordinate change-of-variables statement.

---

## Phase 3 (Stage 5): chart-level change of variables

Goal: state and prove

```lean
theorem iwasawa_change_of_variables
    (f : (Sk n) × ((Fin n → ℝ) × (NN n)) → Matrix (Fin n) (Fin n) ℝ)
    (hf_inj : Function.Injective f)
    -- f is the chart-coordinate version of iwasawaMap
    ...
    {μ : Measure ((Sk n) × ((Fin n → ℝ) × (NN n)))}
    [IsAddHaarMeasure μ]
    {ν : Measure (Matrix (Fin n) (Fin n) ℝ)}
    [IsAddHaarMeasure ν]
    -- with appropriate normalization
    :
    Measure.map f μ = (chart constants) · ν.withDensity (...) := ...
```

This uses `MeasureTheory.Function.Jacobian` lemmas (see §C of
`03_mathlib_api_inventory.md`). The density on the right is
`λ M, |det iwasawaMatrixLeibnizCLM k a u|⁻¹` at the preimage. After
the chart formula, this density is `(2^N · det(a)^n · det(adNN a))^{-1}`.

---

## Phase 4 (Stage 6): Haar formula

Goal: identify the pushforward measure on `G n = GL_n(R)_+` with
mathlib's `MeasureTheory.Measure.haar` up to scalar.

Strategy:
1. Prove the pushforward is left-invariant: use the explicit
   formula and the fact that translation by `g₀ ∈ G n` permutes the
   coordinates correspondingly. Or, alternatively, prove invariance
   directly from the change-of-variables formula.
2. Apply `haarMeasure_unique` to deduce
   `pushforward = c · haar` for some `c > 0`.
3. Optionally normalize `c` by evaluating on a specific compact set.

Or, alternatively:
- Define a measure on `G n` directly via the chart pushforward, then
  prove `IsHaarMeasure` for this measure.
- Use `haarMeasure_eq_iff` to identify with `haar`.

---

## Phase 5 (post-Haar): integration formula and Iwasawa applications

Once Haar is in hand, derive the `dg = a^{2ρ} dk da dn` formula in the
mathlib style as a Fubini-style integration identity:

```lean
theorem haar_decomposition_Iwasawa
    (f : G n → ℝ) (hf : Integrable f μ_haar) :
    ∫ g, f g ∂μ_haar =
      ∫ k, ∫ a, ∫ u, f (iwasawaMap (k, a, u)) ·
        (LinearMap.det (adNN a).toLinearMap) ∂μ_UU ∂μ_A_log ∂μ_K := ...
```

This is the headline "Haar formula for Iwasawa" statement.

---

## Dependency graph

```
Stage 4B2  detInIwasawaBases_one_a_one_eq  [linear algebra only]
   │
   ▼
Stage 4B3  absDetInIwasawaBases_general_eq  [+ translation det facts]
   │
   ▼
Stage 4C   bridge_mfderiv_to_explicit       [uses existing
   │                                         mfderiv_iwasawaMap_at_factored]
   ▼
Stage 5    iwasawa_change_of_variables      [uses MeasureTheory.Function.Jacobian]
   │
   ▼
Stage 6    haar_pushforward                 [uses haarMeasure_unique]
   │
   ▼
Stage 7    haar_decomposition_Iwasawa       [final formula]
```

## What to avoid right now

- Do NOT touch `Mathlib.MeasureTheory.Measure.Haar.*` in Stage 4B2;
  this stage is pure linear algebra.
- Do NOT define `Iwasawa.haar` as a definition before proving the
  pushforward is invariant.
- Do NOT introduce new charts or chart-equivalences in 4B2; stay with
  `iwasawaSourceBasis` (and optionally reindex to a block basis).
- Do NOT add the modular character API.

## Estimated cost (entry-level lemmas already exist)

- Stage 4B2: ~150-300 lines if the block-basis approach goes smoothly;
  the entry lemmas already exist for free.
- Stage 4B3: ~100-200 lines (translation det facts are short).
- Stage 5: ~300-500 lines (Jacobian lemma application with injectivity
  + measurability scaffolding).
- Stage 6+7: ~500-1000 lines (Haar uniqueness + final integration
  identity, plus Fubini sequencing).

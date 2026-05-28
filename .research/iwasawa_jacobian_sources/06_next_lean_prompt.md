# Recommended Next Lean Prompt (Stage 4B2)

The block below is meant to be copy-pasted into a fresh Lean-implementation
session for the `IwasawaCoC` project. It assumes the agent has access to
`iwasawa_change_of_coords/`, that `lake
build` succeeds, and that the research files in
`.research/iwasawa_jacobian_sources/` are readable.

---

```
Implement Stage 4B2 of the IwasawaCoC project: the explicit normalized
determinant formula for the actual derivative of iwasawaMap.

Target theorem (add to IwasawaJacobianExplicit.lean, near the bottom):

  theorem detInIwasawaBases_one_a_one_eq (a : A n) :
      detInIwasawaBases (iwasawaMatrixLeibnizCLM
        ⟨1, IsOrthogonal.one⟩ a ⟨1, IsUpperUnipotent.one⟩) =
        (2 : ℝ) ^ Fintype.card (nnIndex n)
          * (a.1.det) ^ n
          * LinearMap.det (adNN a).toLinearMap

Followed by the trivial absolute-value corollary:

  theorem absDetInIwasawaBases_one_a_one_eq (a : A n) :
      absDetInIwasawaBases (iwasawaMatrixLeibnizCLM
        ⟨1, IsOrthogonal.one⟩ a ⟨1, IsUpperUnipotent.one⟩) =
        (2 : ℝ) ^ Fintype.card (nnIndex n)
          * (a.1.det) ^ n
          * LinearMap.det (adNN a).toLinearMap

Sign note: the prefactor is + (2 : ℝ) ^ N, NOT (-2)^N. This is fixed by
the lex ordering of iwasawaSourceBasis and Matrix.stdBasis. See
.research/iwasawa_jacobian_sources/01_formula_reconciliation.md Q4 and
02_lean_theorem_targets.md for the derivation.

Existing infrastructure to reuse:
  * skBasis           (Basis (nnIndex n) ℝ (Sk n))
  * nnBasis           (Basis (nnIndex n) ℝ (NN n))
  * iwasawaSourceBasis (Basis (Fin n × Fin n) ℝ ((Sk n) × ((Fin n → ℝ) × (NN n))))
  * Entry lemmas:
      iwasawaMatrixLeibnizCLM_one_a_one_source_lower_lower_entry
      iwasawaMatrixLeibnizCLM_one_a_one_source_lower_upper_entry
      iwasawaMatrixLeibnizCLM_one_a_one_source_diag_diag_entry
      iwasawaMatrixLeibnizCLM_one_a_one_source_upper_upper_entry
  * toMatrix-wrapped entry lemmas:
      iwasawaMatrixLeibnizCLM_one_a_one_toMatrix_*_*_entry
  * adNN_det_eq_pair_product (T1-6 explicit pair-product formula)
  * detInIwasawaBases_one_a_one_ne_zero (existing nonvanishing)

Recommended strategy:

(1) Define a "block-ordered" basis that groups each pair {p, q} (p < q)
    into two consecutive positions and lists diagonal positions
    contiguously. Specifically:

      def iwasawaBlockIndex (n : ℕ) : Type :=
        (Fin n) ⊕ (nnIndex n × Bool)
      -- Sum.inl i: diagonal (i, i)
      -- Sum.inr (ij, false): upper-side source (ij.1.1, ij.1.2)
      -- Sum.inr (ij, true):  lower-side source (ij.1.2, ij.1.1)

      def iwasawaBlockIndexEquiv : iwasawaBlockIndex n ≃ Fin n × Fin n := ...

      noncomputable def iwasawaBlockBasis : ... :=
        iwasawaSourceBasis.reindex iwasawaBlockIndexEquiv.symm

(2) Prove via a mathlib lemma (look for the LinearMap.det invariance
    under Basis.reindex; equivalently, det of toMatrix is invariant
    under simultaneous row+column permutation by the SAME equiv) that

      detInIwasawaBases L = (LinearMap.toMatrix iwasawaBlockBasis ...
                              L.toLinearMap).det

    so the determinant doesn't depend on the basis order.

(3) With the block-ordered basis, show the toMatrix is literally a
    block-diagonal matrix:
       - one diagonal block of size n x n, equal to Matrix.diagonal a.1.diag;
       - N pair blocks of size 2 x 2, each equal to
           [ a.1 p p,  -2 * a.1 q q ]
           [   0    ,   2 * a.1 p p ]
         for the pair index (p, q) with p < q.
    Use the entry lemmas mentioned above plus Matrix.ext_iff for
    component-by-component verification.

(4) Apply mathlib block-diagonal determinant facts:
      Matrix.det_diagonal              -- for the n x n diagonal block
      Matrix.det_fromBlocks_zero₂₁     -- for each 2 x 2 pair block
      Matrix.det_blockDiagonal         -- to combine
    OR, equivalently, simultaneously permute rows and columns by the
    block-collation permutation and apply Matrix.det_blockDiagonal.

(5) Combine the block determinants:
      ∏_i a_ii = a.1.det                                    [diagonal]
      ∏_{p<q} 2 * (a.1 p p)^2 = 2^N * ∏_p a_p^{2(n-1-p)}    [pair blocks]

(6) Match the RHS to (2 : ℝ)^N * det(a)^n * det(adNN a):
      det(a)^n = ∏_p a_p^n
      det(adNN a) = ∏_p a_p^{n-1-2p}    (by adNN_det_eq_pair_product)
      Product:    ∏_p a_p^{2n - 1 - 2p}
      Equivalent: det(a) * ∏_p a_p^{2(n-1-p)}
    So the goal collapses to a Finset exponent rearrangement, closeable
    by Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, and
    pow_add as needed (or ring_nf after enough algebra unfolding).

Constraints:
  * Do NOT introduce any sorries or axioms.
  * Do NOT modify any file other than IwasawaJacobianExplicit.lean
    (unless you need a tiny helper lemma in IwasawaCoC.lean or
    IwasawaJacobianAbstract.lean about Matrix.det_diagonal applied to
    positive diagonal matrices; if so, ask first).
  * Do NOT touch Haar measure machinery in this stage.
  * Do NOT generalize beyond (k = 1, u = 1) in this stage; that is
    Stage 4B3.
  * Stay within the `IwasawaCoC` namespace.
  * Use the existing local instance attributes for matrix norms
    (linftyOp*); do not change matrix typeclass setup.
  * Keep `set_option linter.unusedSectionVars false` etc. consistent
    with the rest of the file.

Verification:
  * After implementing, run `lake build` and confirm the new theorem
    compiles.
  * Run an AxiomCheck-style file to verify the new theorem depends only
    on [propext, Classical.choice, Quot.sound] (no new axioms).
  * Update README.md or IwasawaBlockers.md with the new milestone if
    appropriate.

Reference reading (in this order):

  1. .research/iwasawa_jacobian_sources/05_one_page_summary_for_gpt.md
     (dense overview)

  2. .research/iwasawa_jacobian_sources/01_formula_reconciliation.md
     (Q4 has the explicit 2x2-block computation)

  3. .research/iwasawa_jacobian_sources/02_lean_theorem_targets.md
     (Lean signatures, sign note, fallbacks)

  4. .research/iwasawa_jacobian_sources/04_implementation_plan.md
     (Phase 0 has step-by-step strategy)

  5. .research/iwasawa_jacobian_sources/03_mathlib_api_inventory.md
     (relevant mathlib lemmas with file paths)

  6. IwasawaJacobianExplicit.lean
     (existing entry lemmas and adNN_det_eq_pair_product)

  7. MathlibInfrastructureMap.md
     (prior project Lie group infrastructure; mostly NOT relevant for
     this stage but useful background)

Out-of-scope (for a later stage, do NOT do now):

  * Generalize to (k, a, u) with k != 1, u != 1.
  * Bridge to mfderiv via the manifold differential.
  * Apply MeasureTheory.Function.Jacobian.
  * Define or compute Haar measure on G n.
  * Identify the chart pushforward with mathlib's Measure.haar.

Success criterion:

  * detInIwasawaBases_one_a_one_eq and absDetInIwasawaBases_one_a_one_eq
    compile and pass AxiomCheck.
  * RHS exactly matches (2 : ℝ) ^ Fintype.card (nnIndex n) *
    (a.1.det) ^ n * LinearMap.det (adNN a).toLinearMap.
  * detInIwasawaBases_one_a_one_ne_zero remains correct (or is now
    derivable from the new explicit formula).
  * No new sorries, no new axioms, no Haar machinery.
```

---

## Notes for the agent receiving this prompt

- If the block-basis approach (recommended) turns out to be more
  bookkeeping than expected, try the alternative: stay with
  `iwasawaSourceBasis` and compute the determinant via the Leibniz
  formula by identifying the unique nonzero permutation. The matrix is
  block-diagonal after a specific permutation (collect each pair's two
  positions adjacently), and that permutation is even (since it consists
  of disjoint adjacent transpositions, which is even for any number of
  pairs N — wait, each transposition is odd, so N transpositions has
  sign (-1)^N). Re-check this carefully before committing: simultaneous
  row+column permutation by the same permutation does NOT change the
  determinant (sign cancels), so this is a non-issue for the
  block-diagonal route via reindex.

- If the proof gets stuck on the `Finset.prod` exponent rearrangement,
  consider splitting the goal into per-index equalities and using
  induction on `n`.

- Make heavy use of `simp [iwasawaMatrixLeibnizCLM_one_a_one_*_entry]`
  to mechanically compute each block.

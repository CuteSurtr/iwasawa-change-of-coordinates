# L3-A: Textbook factorization citation

## Primary citation

**Lee, John M., *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Ch. 7 Example 7.27 + Prop. 3.14.**

- **Example 7.27 (p. 152, "The General Linear Group"):** Since `GL(n, ℝ)` is an open subset of `M(n, ℝ) ≅ ℝ^(n²)`, the tangent space `T_g GL(n, ℝ)` is canonically identified with `M(n, ℝ)` at every point `g`, with no left-translation required. **This is the project's `mfderiv_subtypeVal_G = id` bridge.**

- **Proposition 3.14 (differential of a bilinear map):** For bilinear `B : V × W → Z`,
  `dB_{(v₀, w₀)}(X, Y) = B(X, w₀) + B(v₀, Y)`.
  Applied to matrix multiplication `μ_M : M_n × M_n → M_n`, this gives the **matrix-Leibniz rule**:
  `d(AB)|_{(A₀, B₀)}(X, Y) = X · B₀ + A₀ · Y`.

Iterating once for triple product `f(A, B, C) = ABC`:
`df|_{(A₀,B₀,C₀)}(X, Y, Z) = X·B₀·C₀ + A₀·Y·C₀ + A₀·B₀·Z`.

This IS the project's target with `(A₀, B₀, C₀) = (k₀, a₀, u₀)`.

## How chart conventions add the chain-rule factors

- **K chart (Cayley right-mul):** `d(cayley)|_0(X) = -2 X` (project's `hasFDerivAt_cayley_zero`), so the K-component contribution is `(-2 X.1) · (k₀.1 · a₀.1 · u₀.1)` after chain rule pulls Cayley derivative through right-mul by `Q₀`.

- **A chart (log/exp diagonal):** `d(diag ∘ exp)|_{a₀ chart center}(v) = a₀ · diag(v)` (chain rule: derivative of `t ↦ diag(exp(log a₀ + tv))` at 0 is `diag(a₀_i · v_i) = a₀ · diag(v)` since `a₀` is diagonal).

- **UU chart (affine +1):** `d(Z ↦ Z + 1)(Z) = Z`, contributing `k₀ · a₀ · Z` after pre/post composition.

Total:
```
dμ(X, v, Z) = -2 X.1 · (k₀.1 a₀.1 u₀.1)
             + k₀.1 · a₀.1 · Matrix.diagonal v · u₀.1
             + k₀.1 · a₀.1 · Z.1
```

This is exactly `iwasawaMatrixLeibnizCLM_apply`. ✓

## Cross-references (consistency check)

**Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., §VI.4, pp. 401-404, Prop. 6.46.**
Proves `μ : K × A × N → G` is a diffeomorphism by showing differential at identity is `(X_K, X_A, X_N) ↦ X_K + X_A + X_N`. At general point invokes left-translation equivariance:
`dμ_{(k₀,a₀,u₀)} = dL_{k₀ a₀ u₀} ∘ dμ_{(1,1,1)} ∘ (...)`.
This is the LEFT-translation form. **Equivalent to matrix-Leibniz for GL_n** because `dL_g(X) = g·X` under the canonical tangent identification — same equation, rearranged.

**Helgason, *DGLGSS*, Ch. II §3 + Ch. IX §1 Theorem 1.3.**
`dμ_{(a,b)}(X, Y) = dR_b(X) + dL_a(Y)`. For GL_n: `XB + AY`. Same Leibniz rule.

**Bump, *Automorphic Forms and Representations*, §2.1.** Works with `GL_n(ℝ) = NAK`; computes Haar measure via Jacobians using `d(AB) = dA·B + A·dB`.

**Jorgenson & Lang, *Spherical Inversion on SL_n(ℝ)*, Theorem 1.1 + Ch. V §3.** Explicit Jacobian of `(u, a, k) ↦ uak` via matrix product rule.

## Why our chart matches the matrix-Leibniz form (no Ad-twist)

The project's three charts are all **global linear charts** on each factor:
- Cayley (with `-2` slope at 0)
- log/exp-diagonal (giving `diag(v)` differential)
- affine `Z ↦ Z + 1`

Composing μ with the three chart inverses and applying matrix-Leibniz once produces the three-term formula. **No Ad-twist appears** because:
(a) The tangent identification on GL_n is **global** (not the left-invariant trivialization).
(b) We differentiate the chart inverses (which land in M_n) and then apply the trilinear product.

The Ad-twist ONLY appears if you first left-translate to the identity and use Lie-algebra coordinates (as in the earlier, incorrect formulation).

**Recommended primary citation for the Lean proof: Lee, ISM 2nd ed., Prop 3.14 + Example 7.27. Apply Prop 3.14 twice for the triple-product Leibniz.**

## Sources

- Knapp Ch. VI: https://www.math.stonybrook.edu/~aknapp/books/green/file4.pdf
- Lee full PDF: https://www.math.colostate.edu/~renzo/teaching/DiffGeo2011/Introduction%20to%20Smooth%20Manifolds%20-%20J.%20Lee.pdf
- Helgason GSM 34: https://bookstore.ams.org/gsm-34
- Jorgenson-Lang PDF: https://vdoc.pub/documents/spherical-inversion-on-sl-n-r-218fuvrtahi0
- Schlichtkrull (KU): https://web.math.ku.dk/~schlicht/Liegroups/IwasawaDecomp.pdf
- nLab: https://ncatlab.org/nlab/show/Iwasawa+decomposition

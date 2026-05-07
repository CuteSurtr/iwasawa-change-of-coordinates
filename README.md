# Iwasawa Decomposition and Change of Coordinates

A Lean 4 / Mathlib formalization of **Theorem 1.1** of

> J. Jorgenson, S. Lang. *Spherical Inversion on `SL_n(R)`*.
> Springer Monographs in Mathematics, 2001.

The Iwasawa product map

```
Φ : K × A × U → GL_n(ℝ),     (k, a, u) ↦ k · a · u
```

is asserted by Jorgenson–Lang to be a *differential isomorphism*
(diffeomorphism), where

- `K = O(n)` is the real orthogonal group,
- `A` is the group of positive diagonal `n × n` real matrices,
- `U` is the group of unipotent upper triangular `n × n` real matrices.

This project formalizes the algebraic, topological, and (largely) smooth
content of that theorem, building on top of the parent project's
[`project.Iwasawa`](../project/Iwasawa.lean), which provides the
set-theoretic existence and uniqueness of the Iwasawa factorization
following Lang's *Linear Algebra*.

## Status at a glance

| Quantity | Value |
|---|---|
| Lines of Lean | 1666 (+ 56-line `AxiomCheck.lean`) |
| `sorry` count | **0** |
| User-declared axioms | 0 |
| Build errors | 0 |
| Build warnings | 0 |
| Axiom dependencies (every named theorem / instance) | `propext`, `Classical.choice`, `Quot.sound` only |
| Theorems / instances tested in `AxiomCheck.lean` | **46** |

Every named theorem and instance in the file is proved without `sorry`
and depends only on the three standard Mathlib axioms.

## Honest disclaimer

We were not able to close out the very last layer of Scope C — the
`IsManifold` instance on the full orthogonal group, the bundled
`iwasawaDiffeomorph`, and the geometric `mfderiv` at the identity.
These pieces require fluency with Mathlib's `ContDiff` / `ContMDiff` /
`isManifold_of_contDiffOn` machinery (specifically the chart-transition
`ContDiffOn` proof for the Cayley atlas, plus set-equality bookkeeping
between the abstract chart-transition source and the concrete
"`1 + ...` is invertible" set) that exceeded our reliable working
knowledge at the time. Each attempt at writing the proof either
introduced `sorry`s (which break Mathlib's warnings-as-errors build) or
got tangled in idiomatic ContDiff / model-with-corners unfolding we
could not resolve.

What is in the file is therefore the entire mathematical content
**up to but not including** that final layer: every Cayley-side
prerequisite (definitions, invertibility, orthogonality, two-sided
inverses, skewness of inverse, set-theoretic equivalence, continuity,
Homeomorph, ChartedSpace, plus a fully proved `C∞` Diffeomorph on the
identity-centered chart `Sk n ≃ K_open n`) is in place and checked.
The `Sphere`-style multi-chart atlas (`instChartedSpaceK`) is also
proved. What remains is the chart-transition smoothness proof and the
`IsManifold` and `Diffeomorph` bundling on top of it. We document the
shape of the missing proof concretely below in
[Remaining work](#remaining-work) so anyone with the right Mathlib
fluency can pick up from where we stopped.

## Provenance and convention

The parent project follows Lang's *Linear Algebra* (3rd edition, 1987)
and writes the Iwasawa decomposition as `g = k · a · u` (orthogonal,
positive-diagonal, upper-unipotent — `K` on the *left*).

Jorgenson–Lang use the opposite order `g = u · a · k` (`K` on the
*right*). The clean change-of-coordinates between the two conventions
is **inversion**: if `g = k · a · u` (Lang), then

```
g⁻¹ = u⁻¹ · a⁻¹ · kᵀ
```

is in J–L form (upper-unipotent · positive-diagonal · orthogonal),
since the inverse of an upper-unipotent matrix is upper-unipotent, the
inverse of a positive diagonal matrix is positive diagonal, and the
transpose of an orthogonal matrix is orthogonal.

The Cartan involution `θ : g ↦ (gᵀ)⁻¹` is a separate involution that
J–L use on p. 2 to characterize `K` as its fixed-point subgroup. We
formalize both.

## Mathematical motivation: why the Iwasawa decomposition is a change of coordinates

### From decomposition to coordinates

`GL_n(ℝ)` is an open subset of the `n²`-dimensional matrix space
`Mat_n(ℝ)`, so as a manifold it is `n²`-dimensional. The three
subgroups in the Iwasawa decomposition contribute exactly the right
dimensions to add up to `n²`:

```
dim K = dim O(n)              = n(n−1)/2     (skew-symmetric matrices)
dim A = dim {pos. diagonals}  = n            (one positive real per diagonal entry)
dim U = dim {upper unipotent} = n(n−1)/2     (strictly-upper entries)
                                ───────
                                  n²
```

The product map

```
Φ : K × A × U → GL_n(ℝ),     Φ(k, a, u) = k · a · u
```

is therefore a map between two manifolds of equal dimension. The
content of Theorem 1.1 is that `Φ` is not merely a bijection but a
*differential isomorphism* (diffeomorphism). What this **really
means** is that `(k, a, u)` is a **system of global coordinates**
on `GL_n(ℝ)` — or equivalently, that the Iwasawa decomposition
gives a *change of coordinates* from the ambient matrix entries
`(g_{ij})` to the triple `(k, a, u)`.

This is more than a curiosity. The Iwasawa coordinates are far
better adapted to the structure of the group than the ambient
entries: `K` carries a compact Lie group structure, `A` is a free
abelian group `(ℝ⁺)ⁿ`, and `U` is a unipotent group on which the
exponential map is a *polynomial* diffeomorphism with the Lie
algebra of strictly-upper triangular matrices. Many constructions
in representation theory, harmonic analysis on Lie groups, and
spherical-function theory either *cannot* or are dramatically
harder to express in the ambient `(g_{ij})` coordinates and become
natural in the Iwasawa coordinates.

### The Jacobian bridge: invariant measure transforms by the Iwasawa character

The classical bridge between "Iwasawa decomposition" and
"change-of-coordinates Jacobian" is the **Haar-measure
decomposition formula**. If `dx` is a (left) Haar measure on
`G = GL_n(ℝ)`, `du`, `da`, `dk` are Haar measures on `U`, `A`, `K`,
and the product map `U × A × K → UAK = G` is the J–L Iwasawa map,
then for any `f ∈ C_c(G)`

```
∫_G f(x) dx = c · ∫_U ∫_A ∫_K f(uak) · δ(a)⁻¹ du da dk
```

for a constant `c` and a homomorphism `δ : A → ℝ⁺` called the
**Iwasawa character**. (J–L Proposition 2.1, 2.3, 2.4.) The
Jacobian factor is precisely `δ(a)⁻¹`: changing variables from
`x ∈ G` to `(u, a, k) ∈ U × A × K` introduces the determinant of
the differential of the Iwasawa map, which equals `δ(a)` (up to the
constant `c`).

For `G = GL_n(ℝ)` with the standard upper-unipotent / positive-diagonal /
orthogonal Iwasawa data, J–L's explicit formula (Equation (3) of §I.2)
gives

```
δ(a) = ∏_{i<j} (a_i / a_j) = ∏_{i=1}^{n} a_i^{n − 2i + 1}.
```

This is the **explicit Jacobian** of the change of coordinates from
ambient matrix entries to Iwasawa coordinates `(u, a, k)`. The
proof is a direct computation: `δ(a)` is the determinant of the
conjugation action of `a ∈ A` on the Lie algebra `𝔫 = Lie(U)` of
strictly upper-triangular matrices, because the Lie algebra `𝔫`
is the *tangent space to U at the identity*, and the change-of-
variable formula on a Lie group near a point is governed by the
adjoint action on the Lie algebra (J–L Equations (1)–(3) of §I.2).
The eigenvalues of `Ad(a)` on the basis `E_{ij}` (`i < j`) of `𝔫`
are exactly the characters `χ_{ij}(a) = a_i / a_j`, and `δ(a)` is
the product of these.

### Why a *differential* isomorphism (not just a bijection)

A bijection just renames points: it lets you say "every `g` has a
unique `(k, a, u)`". A homeomorphism additionally guarantees that
the renaming is continuous in both directions: convergence of `g_n`
to `g` translates to convergence of `(k_n, a_n, u_n)` to `(k, a, u)`.
A *diffeomorphism* additionally guarantees that the renaming is
**smooth in both directions**: derivatives, vector fields, and
integrals all transform correctly under the change of coordinates.

For our purposes, only the diffeomorphism level is strong enough to
support the Haar-measure decomposition formula: the Jacobian of a
change of coordinates is the absolute value of the determinant of
the differential of the change, so without a *differential*
isomorphism we cannot even *state* the Jacobian formula. This is
why Theorem 1.1 of Jorgenson–Lang asserts a **differential**
isomorphism, and why our project's central technical content is
the smooth-manifold story (the Cayley transform giving a
diffeomorphism `Sk n ≃ K_open n`, and the Sphere-pattern multi-chart
atlas covering all of `K = O(n)`).

### Connection to the Lie algebra: infinitesimal change of coordinates

Every smooth change of coordinates on a Lie group induces an
**infinitesimal change of coordinates** at the identity, namely a
linear isomorphism between Lie algebras. For the Iwasawa map
`Φ : K × A × U → G`, the differential at the identity
`(1, 1, 1) ∈ K × A × U` is a linear map

```
dΦ_(1,1,1) : 𝔨 × 𝔞 × 𝔫 → 𝔤𝔩_n(ℝ),     (X, Y, Z) ↦ X + Y + Z
```

where `𝔨 = Lie(K) = {skew-symmetric matrices} = Sk_n`,
`𝔞 = Lie(A) = {real diagonal matrices}`,
`𝔫 = Lie(U) = {strictly upper-triangular matrices}`.

For `dΦ_(1,1,1)` to be a linear isomorphism, the three subspaces
`𝔨, 𝔞, 𝔫` must form a **direct sum decomposition** of `𝔤𝔩_n(ℝ)`.
This is the **Iwasawa Lie decomposition**:

```
𝔤𝔩_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫.
```

This is the *purely linear-algebraic shadow* of Theorem 1.1, and
has the same dimension count (`n(n−1)/2 + n + n(n−1)/2 = n²`) and
the same role: it expresses every matrix as a sum of a skew, a
diagonal, and a strictly upper-triangular piece in a unique way.
The decomposition is also the natural setting for the structure
theory of semisimple Lie algebras (root spaces, parabolic
subalgebras, Borel subalgebras, etc.).

The closely-related **Cartan Lie decomposition** is the coarser
splitting

```
𝔤𝔩_n(ℝ) = Sym_n ⊕ Sk_n
```

into symmetric and skew-symmetric parts. The Iwasawa decomposition
*refines* the symmetric component into `𝔞 ⊕ 𝔫_sym`, where
`𝔫_sym = (1/2)(𝔫 + 𝔫ᵀ)` is the symmetrization of the strictly
upper-triangular subalgebra (J–L §I.3, p. 14).

In this project we prove both the Iwasawa Lie decomposition
(`iwasawaLieDecomp` and `iwasawaLieEquiv`) and the Cartan Lie
decomposition (`cartanLieDecomp`). The geometric statement
"`dΦ_(1,1,1)` equals the linear sum map" is the content of the
deferred `iwasawaMap_mfderiv_at_one`; what we prove
algebraically is exactly the statement that *the candidate linear
map* `(X, Y, Z) ↦ X + Y + Z` is a `LinearEquiv`. Once the smooth
manifold structure on the full `K = O(n)` is in place, the
geometric statement follows from a direct Jacobian computation of
the Cayley chart at `0 ∈ Sk` (whose first-order Taylor expansion
is `cayley(X) = 1 + 2X + O(X²)`).

## The mathematics formalized in this project

The remainder of this section walks through every theorem,
definition, and instance in the file in mathematical detail, in
the order they appear in `IwasawaCoC.lean`. (See [Theorem
statements](#theorem-statements) below for the exact Lean
signatures, and [Proof outlines](#proof-outlines) for the
proof-level summaries.)

### 1. The Iwasawa decomposition: `K × A × U ≃ GL_n(ℝ)`

The starting point. Every invertible real `n × n` matrix `g` admits
a unique factorization

```
g = k · a · u           (k ∈ O(n), a positive diagonal, u upper unipotent).
```

The proof goes through Gram–Schmidt orthonormalization: write `g`'s
columns as a tuple of vectors `(v_1, …, v_n)`, run the Gram–Schmidt
procedure to produce an orthonormal basis `(e_1', …, e_n')` of `ℝⁿ`,
let `Q` be the matrix of `e_i'` (orthogonal), and `R = Qᵀ g` (upper
triangular with positive diagonal). Then `R = a · u` for `a` the
diagonal of `R` and `u = a⁻¹ R` upper unipotent. Set `k = Q`.

Uniqueness comes from a clever orthogonality argument: an
orthogonal upper-triangular matrix with positive diagonal must be
the identity. This existence + uniqueness is the parent project
[`project.Iwasawa`](../project/Iwasawa.lean), which we wrap as
`iwasawaEquiv : K × A × U ≃ GL_n(ℝ)`.

The mathematical content "Iwasawa decomposition is QR
decomposition" should be appreciated here: in numerical linear
algebra parlance this *is* the QR factorization, and the
Iwasawa-coordinate Jacobian formula above is the Jacobian of QR
in disguise.

### 2. Convention swap (Lang ↔ Jorgenson–Lang) and the Cartan involution

The convention swap is a useful exercise in matrix algebra. Lang
writes `g = k · a · u`. J–L write `g = u · a · k`. These are *not*
related by simply re-labeling factors of the *same* `g`: they are
two different factorizations.

The connection is **inversion**: if `g = kau` in Lang form, then
taking inverses

```
g⁻¹ = u⁻¹ · a⁻¹ · k⁻¹ = u⁻¹ · a⁻¹ · kᵀ
```

(using `k⁻¹ = kᵀ` for orthogonal `k`). The right-hand side is in
J–L form, since:

* `u⁻¹` is upper-unipotent (the inverse of an upper-unipotent
  matrix is upper-unipotent — easy proof by induction on `n` or by
  explicitly truncating the geometric series),
* `a⁻¹` is positive diagonal (diagonal entries `1/a_i > 0`),
* `kᵀ` is orthogonal (`kᵀ · (kᵀ)ᵀ = kᵀ k = 1`).

So **inversion** is the change of coordinates between Lang's `g`
and J–L's `g⁻¹`. This is `inv_iwasawa_jl`.

The **Cartan involution** is a *different* operation:

```
θ : GL_n(ℝ) → GL_n(ℝ),     θ(g) = (gᵀ)⁻¹ = (g⁻¹)ᵀ.
```

It is an order-2 group automorphism (`cartanInvolution_involutive`).
J–L use it on p. 2 to characterize the orthogonal subgroup as its
fixed-point set:

```
K = { g ∈ GL_n(ℝ) | θ(g) = g }
   = { g ∈ GL_n(ℝ) | (gᵀ)⁻¹ = g }
   = { g ∈ GL_n(ℝ) | g · gᵀ = 1 }
```

which is exactly the orthogonality condition. The Cartan involution
also induces an involution `θ_*` on the Lie algebra `𝔤𝔩_n(ℝ)` whose
fixed-point set is `𝔨 = Sk_n` and whose `−1`-eigenspace is `𝔭 = Sym_n`,
giving the **Cartan Lie decomposition** `𝔤𝔩_n = 𝔨 ⊕ 𝔭` of Milestone 4.

### 3. Topology: the Iwasawa map is a homeomorphism

The forward direction of continuity is straightforward: matrix
multiplication `(k, a, u) ↦ k · a · u` is jointly continuous (a
finite product of bilinear matrix-multiplication operations,
each of which is continuous by `Continuous.matrix_mul`), and we
embed the result back into the open subtype `GL_n(ℝ)` via
`Continuous.subtype_mk`. This gives `continuous_iwasawaMap`.

The inverse direction is substantially harder, and is the most
technically interesting topological content of the project. Given
`g ∈ GL_n(ℝ)`, we need to show that the maps `g ↦ k`, `g ↦ a`,
`g ↦ u` are continuous. Each of these is built from Gram–Schmidt
orthonormalization applied to the columns of `g`, so we are
asking: **is Gram–Schmidt continuous in its input function?**

The answer is yes — on the open set of input tuples that are
linearly independent. The intuition: the Gram–Schmidt outputs are
rational functions of the input vectors, with positive denominators
(norms of intermediate vectors) on the linearly-independent locus,
so they are continuous (in fact smooth). Concretely, Wikipedia's
"Gram–Schmidt process" article gives an explicit determinantal
formula:

```
u_j = (1 / D_{j-1}) · det
        ⎛ ⟨v_1, v_1⟩  ⟨v_2, v_1⟩  ⋯  ⟨v_j, v_1⟩ ⎞
        ⎜    ⋮            ⋮         ⋱     ⋮      ⎟
        ⎜ ⟨v_1, v_{j−1}⟩ ⋯           ⟨v_j, v_{j−1}⟩ ⎟
        ⎝    v_1          v_2       ⋯    v_j        ⎠
```

where `D_{j−1}` is the Gram determinant of the previous vectors.
Since each entry is a polynomial in the `v_i`'s and `D_{j−1} > 0`
on the linearly-independent locus, each `u_j` is rational with
non-vanishing denominator there, hence continuous.

Mathlib does **not** package this continuity result. We prove it
inline by induction on the index `i : Fin n` using
`gramSchmidt_def`, which expresses

```
gramSchmidt(f)(i) = f(i) − Σ_{j < i} (𝕜 ∙ gramSchmidt(f)(j)).starProjection (f(i)).
```

Each term in the sum is continuous in `f` by induction (the
projection onto a 1-dimensional subspace is the rational expression
`(⟨v, w⟩ / ‖v‖²) · v` via `Submodule.starProjection_singleton`,
which is continuous when `‖v‖ ≠ 0` — and the previous Gram–Schmidt
outputs are nonzero on the linearly-independent locus).

This is the proof of `continuous_gramSchmidt_at`, which feeds into
`continuous_qMat_subtype`, `continuous_dMat_subtype`,
`continuous_uMat_subtype`, and finally `continuous_iwasawaSymm`.
Combining with the forward continuity gives `iwasawaHomeomorph`.
(This continuity result for `gramSchmidt`/`gramSchmidtNormed` is
itself a candidate Mathlib upstream contribution.)

### 4. Smooth structures on the easy three subgroups

The three "easy" subgroups admit single-chart smooth structures.

**`G n = GL_n(ℝ)` as an open submanifold of `Mat_n(ℝ)`:** the
determinant map is continuous, so `{g : Mat_n(ℝ) | g.det ≠ 0}` is
open in `Mat_n(ℝ)`. Hence `G n` is an open submanifold modeled on
`Mat_n(ℝ)`, with smooth structure provided by Mathlib's
`IsOpenEmbedding.singletonChartedSpace` and
`IsOpenEmbedding.isManifold_singleton`. The norm on `Mat_n(ℝ)` is
chosen via `attribute [local instance]` as the standard sup-of-sup
norm `Matrix.normedAddCommGroup` (Mathlib intentionally does not
register a canonical matrix norm globally because several natural
choices exist). This is `instChartedSpaceG`, `instIsManifoldG`.

**`UU n` as an affine slice of `Mat_n(ℝ)`:** an upper-unipotent
matrix is `1 + X` for `X` strictly upper triangular (i.e.,
`X ∈ NN n = 𝔫`), so the natural chart is the *translation*

```
UU n → NN n,     U ↦ U − 1
```

with inverse `X ↦ X + 1`. Both maps are continuous (subtraction
and addition by a constant matrix), and the bijection is the
homeomorphism `UU.toNNHomeomorph`. The chart's source is all of
`UU n`, so we can use
`OpenPartialHomeomorph.singletonChartedSpace` to get
`ChartedSpace (NN n) (UU n)` and `IsManifold` modeled on the
normed space `NN n` (a `Submodule` of `Mat_n(ℝ)`).

**`A n` via diagonal logs:** a positive diagonal matrix is
characterized by its `n` strictly-positive diagonal entries; the
homeomorphism

```
A n → ℝⁿ,     D ↦ (log D_{11}, …, log D_{nn})
```

with inverse `v ↦ diag(exp v_1, …, exp v_n)` provides a single
chart. The map is well-defined because `D_{ii} > 0`, so `log` is
continuous, and `exp v_i > 0` for all real `v_i`, so the inverse
lands back in `A n`. This is `A.toFinNRHomeomorph`. Modeled on
`Fin n → ℝ` (Pi-normed space).

### 5. The Cayley transform: parametrizing `O(n)` by skew-symmetric matrices

The hard subgroup is `K = O(n)`. Unlike `G`, `A`, `UU`, the
orthogonal group is not a single coordinate chart's worth of
material: it is a **compact closed submanifold** cut out by the
quadratic equations `Q · Qᵀ = 1`. Single charts cannot cover
compact manifolds (the image would be both compact and
homeomorphic to an open subset of a Euclidean space, which is
impossible for compact manifolds of positive dimension).

The standard way around this is the **Cayley transform**, due to
Cayley (1846):

```
cayley : Mat_n(ℝ) → Mat_n(ℝ),     cayley(X) = (1 − X)(1 + X)⁻¹.
```

Two crucial facts:

1. **`(1 + X)` is invertible whenever `X` is skew-symmetric.** This
   is `one_add_skew_isUnit`. Proof: `(1 + X)(1 − X) = 1 − X²` and
   since `X` is skew, `X² = −X · Xᵀ`, so `1 − X² = 1 + X · Xᵀ`. The
   matrix `X · Xᵀ` is positive semi-definite (it is the Gram matrix
   of the rows of `X`), so `1 + X · Xᵀ` is positive definite, in
   particular invertible. Taking determinants of `(1 + X)(1 − X) =
   1 + X · Xᵀ` shows `det(1 + X)² > 0`, so `det(1 + X) ≠ 0`.

2. **`cayley(X)` is orthogonal whenever `X` is skew-symmetric.**
   This is `cayley_isOrthogonal`. Proof: a direct computation using
   that `(1 − X)`, `(1 + X)` and their inverses all commute (because
   they are polynomials in `X`):

   ```
   cayley(X) · cayley(X)ᵀ = (1 − X)(1 + X)⁻¹ · ((1 + X)⁻¹)ᵀ (1 − X)ᵀ
                          = (1 − X)(1 + X)⁻¹ · (1 + Xᵀ)⁻¹(1 − Xᵀ)
                          = (1 − X)(1 + X)⁻¹ · (1 − X)⁻¹(1 + X)
                          = (1 − X)(1 − X)⁻¹ · (1 + X)⁻¹(1 + X)
                          = 1.
   ```

In words: as `X` ranges over skew-symmetric matrices `Sk n`, the
formula `cayley(X) = (1 − X)(1 + X)⁻¹` ranges over orthogonal
matrices `Q` for which `1 + Q` is invertible (i.e., `−1` is not an
eigenvalue of `Q`). This is a dense open subset of `O(n)`, called
`K_open n` in our file.

The transform is **its own inverse**: applying `cayley` twice
returns the input (when both `1 + X` and `1 + cayley(X)` are
invertible). This is `cayley_self_inverse`, proved by deriving
the algebraic identity

```
1 − cayley(X) = X · (1 + cayley(X))
```

(which holds for any `X` with `1 + X` invertible, and follows from
the two key Cayley identities `(1 ± cayley(X))(1 + X) = (something
linear in X)` proved as `one_add_cayley_mul` and
`one_sub_cayley_mul`), then dividing both sides by
`1 + cayley(X)` (also invertible).

Since `cayley` and `cayleyInv` have *the same formula*
`(1 − M)(1 + M)⁻¹` (one is just the name we give to the function
when going one direction or the other), `cayley_self_inverse`
immediately gives both `cayleyInv ∘ cayley = id_{Sk}` and
`cayley ∘ cayleyInv = id_{K_open}`. Bundling these gives
`cayleyEquiv : Sk n ≃ K_open n` (set-theoretic bijection).

For the **continuity** of Cayley, both directions reduce to
continuity of matrix inversion on units, which Mathlib provides
via `continuousAt_matrix_inv` (matrix inverse is continuous at
any non-singular matrix) plus `NormedRing.inverse_continuousAt`
(the abstract `Ring.inverse` is continuous at any unit). Bundling
gives `cayleyHomeomorph : Sk n ≃ₜ K_open n`.

For the **smoothness** (i.e., `C∞`-ness), the same matrix-inverse-
on-units lemmas give `ContDiff` smoothness of the underlying
matrix-valued formulas; lifting to `ContMDiff` between manifolds
modeled on `Sk n` (with `K_open n` modeled via the Cayley chart
itself) is achieved through `contMDiff_isOpenEmbedding` and
`contMDiffOn_isOpenEmbedding_symm` plus a function-equality
identification. Bundling all of this gives `cayleyDiffeomorph :
Sk n ≃ₘ K_open n` — a `C∞` diffeomorphism between the
skew-symmetric matrices and the dense open subset of `O(n)`.

### 6. The Sphere-pattern multi-chart atlas covering all of `K = O(n)`

Cayley centered at the identity covers `K_open n`, the open subset
where `1 + Q` is invertible. To cover the rest of `O(n)` we follow
Mathlib's `Sphere.lean` pattern (Heather Macbeth, 2021): put a
Cayley chart **at every point** of `K`.

The translated Cayley chart at `Q₀ ∈ K` is

```
chart_{Q₀} : K → Sk,     chart_{Q₀}(Q) = cayleyInv(Q · Q₀ᵀ),
```

defined on the open subset `K_open_at Q₀ = { Q ∈ K | 1 + Q · Q₀ᵀ
invertible }`. The inverse goes `X ↦ cayley(X) · Q₀`. This is a
direct generalization of the identity-centered chart and reduces to
it via the substitution `Q' = Q · Q₀ᵀ` (which sends `K_open_at Q₀`
to `K_open` bijectively). The `cayleyEquivAt` in our file packages
this as `Sk n ≃ K_open_at Q₀`.

The crucial covering property: **every `Q ∈ K` lies in
`K_open_at Q` itself**, because `Q · Qᵀ = 1` and `1 + 1 = 2 · 1`
has determinant `2ⁿ ≠ 0`. This is `self_mem_K_open_at`. So the
family `{ K_open_at Q | Q ∈ K }` is an open cover of `K`, and the
chart at `Q` is `cayleyOpenChartAt Q`. Atlas: take all
`cayleyOpenChartAt Q₀` for `Q₀` ranging over `K`.

This is `instChartedSpaceK`. The resulting `ChartedSpace (Sk n) (K n)`
gives `K = O(n)` a topological manifold structure modeled on the
skew-symmetric matrices. The `IsManifold` instance —
i.e., the smoothness of all chart-transition maps — is the
deferred `instIsManifoldK`. The transition is

```
chart_{Q₁} ∘ (chart_{Q₀})⁻¹ : X ∈ Sk ↦ cayleyInv(cayley(X) · Q₀ · Q₁ᵀ),
```

defined on the open subset of `Sk n` where `1 + cayley(X) · Q₀ · Q₁ᵀ`
is invertible. This is a composition of three smooth pieces (cayley,
right-multiplication by a fixed orthogonal matrix, cayleyInv), and
its smoothness reduces to standard `ContDiff` lemmas about matrix
multiplication and matrix inversion on units, plus
`isManifold_of_contDiffOn` to lift to `IsManifold`.

### 7. The Cartan Lie decomposition `gl_n(ℝ) = Sym_n ⊕ Sk_n`

This is the simplest of the Lie-algebra-side decompositions and a
classical fact: every real square matrix is the sum of a symmetric
and a skew-symmetric matrix in a unique way. The decomposition is

```
M = (1/2)(M + Mᵀ) + (1/2)(M − Mᵀ),
```

with the symmetric part `(1/2)(M + Mᵀ) ∈ Sym_n` and the
skew-symmetric part `(1/2)(M − Mᵀ) ∈ Sk_n`. Uniqueness: if
`M ∈ Sym ∩ Sk` then `Mᵀ = M = −M`, so `2M = 0`, so `M = 0`.

In Lean this is `cartanLieDecomp : IsCompl (Sym n) (Sk n)`, where
`IsCompl` is the lattice-theoretic statement that `Sym ∩ Sk = ⊥`
(the disjoint condition) and `Sym ⊔ Sk = ⊤` (the sum-is-everything
condition). `Sym` and `Sk` are realized as `Submodule ℝ Mat_n(ℝ)`.

This is exactly the Cartan decomposition in the sense of Lie
theory: `Sk_n = Lie(O(n)) = 𝔨` is the maximal compact subalgebra,
and `Sym_n = 𝔭` is the orthogonal complement under the trace form.
The corresponding Cartan involution on the Lie algebra is `θ_*(M)
= −Mᵀ`, with `+1` eigenspace `𝔨` and `−1` eigenspace `𝔭`.

### 8. The Iwasawa Lie decomposition `gl_n(ℝ) = 𝔨 ⊕ 𝔞 ⊕ 𝔫`

This is the Lie-algebra shadow of the Iwasawa group decomposition,
and the most substantial piece of pure linear algebra in the
project. The three subspaces are

```
𝔨 = Sk_n     (skew-symmetric matrices, `Lie(O(n))`)
𝔞 = AA_n     (real diagonal matrices, `Lie(positive diagonals)`)
𝔫 = NN_n     (strictly upper-triangular matrices, `Lie(upper unipotent)`)
```

with dimensions `n(n−1)/2 + n + n(n−1)/2 = n²` summing to
`dim 𝔤𝔩_n(ℝ)`.

We prove the four conditions for an internal direct-sum
decomposition:

* `disjoint_AA_NN`: `𝔞 ∩ 𝔫 = 0`. A diagonal-and-strictly-upper
  matrix has zero off-diagonal entries (by `𝔞`) and zero diagonal
  entries (by `𝔫`), so it is the zero matrix.
* `disjoint_KK_AA`: `𝔨 ∩ 𝔞 = 0`. A skew diagonal matrix has
  `M_{ii} = −M_{ii}` (skew), so `M_{ii} = 0`, and zero off-diagonal
  by diagonality.
* `disjoint_KK_NN`: `𝔨 ∩ 𝔫 = 0`. Below the diagonal, strict-upper
  membership gives `M_{ij} = 0`. On and above the diagonal we use
  skew-symmetry: at `(j, i)` for `i < j` we have `M_{ji} = 0` (below
  diagonal), and skew gives `M_{ij} = −M_{ji} = 0`.
* `iwasawa_codisjoint`: `𝔨 + 𝔞 + 𝔫 = 𝔤𝔩_n(ℝ)`. For any `M`, we
  construct the explicit decomposition
  ```
  A_{ij} = M_{ii} if i = j else 0           (diagonal of M)
  K_{ij} = M_{ij} if j < i, −M_{ji} if i < j, else 0   (skew lower part)
  N_{ij} = M_{ij} + M_{ji} if i < j else 0  (symmetrized strict upper part)
  ```
  and verify `A + K + N = M` on each of the three cases
  (`j < i`, `j = i`, `i < j`).

These four conditions, combined, give `iwasawaLieDecomp`, the full
internal direct-sum statement.

### 9. The algebraic differential at the identity: `KK × AA × NN ≃ gl_n`

The Lie-algebra version of "the Iwasawa map is a diffeomorphism"
is "the Lie sum map is a linear isomorphism." We define

```
iwasawaLieMap : 𝔨 × 𝔞 × 𝔫 →ₗ[ℝ] 𝔤𝔩_n(ℝ),    (X, Y, Z) ↦ X + Y + Z
```

and prove:

* `iwasawaLieMap_surjective` — every `M ∈ 𝔤𝔩_n(ℝ)` is in the image,
  immediately from `iwasawa_codisjoint`.
* `iwasawaLieMap_injective` — the kernel is trivial. Suppose
  `X + Y + Z = 0` with `X` skew, `Y` diagonal, `Z` strict upper.
  By the entry-wise trichotomy:
    * `j < i`: `Y_{ij} = 0` (off-diagonal of a diagonal),
      `Z_{ij} = 0` (`j ≤ i` triggers strict-upper zero), so
      `X_{ij} = 0`.
    * `j = i`: skew says `X_{ii} = −X_{ii}`, so `X_{ii} = 0`, and
      similarly the other two are zero on the diagonal.
    * `i < j`: by the previous case at `(j, i)` we have `X_{ji} = 0`;
      skew gives `X_{ij} = −X_{ji} = 0`. The remaining `Y_{ij}` and
      `Z_{ij}` are zero by the same arguments as above.
  So `X = Y = Z = 0`.
* `iwasawaLieEquiv` bundles these as `LinearEquiv.ofBijective`.

This is the **algebraic differential at the identity** of the
Iwasawa map. The deferred geometric statement `iwasawaMap_mfderiv_at_one`
would identify `mfderiv (iwasawaMap) (1, 1, 1)` with `iwasawaLieEquiv`
(modulo Cayley's first-order Taylor expansion contributing a factor
of `2`).

This linear isomorphism is the "infinitesimal change of coordinates"
between the ambient Lie algebra `𝔤𝔩_n(ℝ)` and the Iwasawa Lie
factor `𝔨 × 𝔞 × 𝔫`. It is the Lie-algebra-level Jacobian of the
Iwasawa map at the identity — and the inverse map `M ↦ (K, A, N)`
gives the explicit formulas above.

## Milestones

| # | Goal | Status | J–L reference |
|---|------|--------|---------------|
| 1   | `iwasawaEquiv : K × A × U ≃ GL_n(ℝ)` (set-theoretic bijection)                   | ✅ proved   | Thm I.1.1, set-theoretic |
| 1b  | `inv_iwasawa_jl`: `(kau)⁻¹ = u⁻¹ a⁻¹ kᵀ` (Lang ↔ J-L convention swap)            | ✅ proved   | §I.1, p. 2              |
| 1b  | `cartanInvolution`, `cartanInvolution_involutive`                                | ✅ proved   | §I.1, p. 2              |
| 2   | `continuous_iwasawaMap` (forward direction)                                      | ✅ proved   | Thm I.1.1, topology     |
| 2   | `continuous_iwasawaSymm` (inverse direction; Gram–Schmidt continuity from scratch) | ✅ proved | Thm I.1.1, topology     |
| 2   | `iwasawaHomeomorph : K × A × U ≃ₜ GL_n(ℝ)`                                       | ✅ proved   | Thm I.1.1, topology     |
| 3   | `isOpen_G`, `G_isOpenEmbedding`, smooth structure on `G n`                       | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `UU.toNNHomeomorph`, smooth structure on `UU n` (modeled on `NN n`)              | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `A.toFinNRHomeomorph`, smooth structure on `A n` (modeled on `Fin n → ℝ`)        | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | Cayley transform setup (`cayley`, `cayleyInv`, `one_add_skew_isUnit`, `cayley_isOrthogonal`) | ✅ proved   | Cayley 1846             |
| 3   | Cayley two-sided inverse (`cayley_self_inverse`, `cayleyInv_cayley`, `cayley_cayleyInv`) | ✅ proved   | Cayley 1846             |
| 3   | `cayleyInv_isSkew` (image of orthogonal under Cayley is skew)                    | ✅ proved   | Cayley 1846             |
| 3   | `cayleyEquiv : Sk n ≃ K_open n` (set-level Cayley bijection)                     | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | Cayley continuity (`continuous_cayley_on_skew`, `continuous_cayleyInv_on_KOpen`) | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `cayleyHomeomorph : Sk n ≃ₜ K_open n` (topological)                              | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | Smooth manifold structure on `K_open n` modeled on `Sk n` via Cayley chart       | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `cayleyDiffeomorph : Sk n ≃ₘ K_open n` (`C∞` diffeomorphism)                     | ✅ proved   | Thm I.1.1, smoothness   |
| 3   | `IsOrthogonal.mul`, `K_open_at`, `cayleyEquivAt Q₀ : Sk n ≃ K_open_at Q₀`        | ✅ proved   | Thm I.1.1, multi-chart  |
| 3   | `self_mem_K_open_at` (cover `⋃ K_open_at Q = K n`)                                | ✅ proved   | Thm I.1.1, multi-chart  |
| 3   | `cayleyOpenChartAt Q₀ : OpenPartialHomeomorph (K n) (Sk n)` + `instChartedSpaceK` | ✅ proved   | Sphere-pattern atlas    |
| 3   | `instIsManifoldK` (chart-transition `ContDiffOn` + IsManifold compatibility)     | ⚠️ deferred | Thm I.1.1, full         |
| 3   | `iwasawaDiffeomorph : K × A × U ≃ₘ GL_n(ℝ)` (full diffeomorphism)                | ⚠️ deferred | Thm I.1.1, full         |
| 4   | `cartanLieDecomp : IsCompl (Sym n) (Sk n)` (Cartan Lie decomp `gl_n = Sym ⊕ Sk`) | ✅ proved   | §I.3, p. 12             |
| 5   | `disjoint_AA_NN`, `disjoint_KK_AA`, `disjoint_KK_NN` (pairwise disjoint)         | ✅ proved   | §I.3                    |
| 5   | `iwasawa_codisjoint`: `𝔨 ⊔ 𝔞 ⊔ 𝔫 = ⊤` (sum is everything)                         | ✅ proved   | §I.3                    |
| 5   | `iwasawaLieDecomp`: full Iwasawa Lie decomposition `gl_n = 𝔨 ⊕ 𝔞 ⊕ 𝔫`            | ✅ proved   | §I.3                    |
| 5   | `iwasawaLieEquiv`: linear iso `𝔨 × 𝔞 × 𝔫 ≃ₗ[ℝ] gl_n(ℝ)` (algebraic differential at 1) | ✅ proved | §I.3                    |
| 5   | `iwasawaMap_mfderiv_at_one` (full geometric `mfderiv` at identity)               | ⚠️ deferred | §I.3                    |

The legend `⚠️ deferred` means: the mathematical statement is documented
in the file with a precise outline of the proof, but the proof itself
was not closed then, due to the Mathlib-fluency obstacles
described in the [honest disclaimer](#honest-disclaimer) above.

## Theorem statements

```lean
namespace IwasawaCoC

/-- Subgroup types as bundled subtypes of `Matrix (Fin n) (Fin n) ℝ`. -/
abbrev K (n : ℕ) := { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q }
abbrev A (n : ℕ) := { D : Matrix (Fin n) (Fin n) ℝ // IsPositiveDiagonal D }
abbrev UU (n : ℕ) := { u : Matrix (Fin n) (Fin n) ℝ // IsUpperUnipotent u }
abbrev G (n : ℕ) := { g : Matrix (Fin n) (Fin n) ℝ // g.det ≠ 0 }

/-- Milestone 1: set-theoretic Iwasawa bijection. -/
def iwasawaMap : K n × A n × UU n → G n
noncomputable def iwasawaEquiv : K n × A n × UU n ≃ G n

/-- Milestone 1b: convention swap (Lang ↔ J-L) via inversion. -/
theorem inv_iwasawa_jl (k : K n) (a : A n) (u : UU n) :
    (k.1 * a.1 * u.1)⁻¹ = u.1⁻¹ * a.1⁻¹ * k.1.transpose

/-- Milestone 1b: Cartan involution θ(g) = (gᵀ)⁻¹ and its involutivity. -/
noncomputable def cartanInvolution : G n → G n
theorem cartanInvolution_involutive :
    Function.Involutive (cartanInvolution : G n → G n)

/-- Milestone 2: forward and inverse continuity, then Homeomorph. -/
theorem continuous_iwasawaMap : Continuous (iwasawaMap : K n × A n × UU n → G n)
theorem continuous_iwasawaSymm : Continuous (iwasawaEquiv (n := n)).symm
noncomputable def iwasawaHomeomorph : K n × A n × UU n ≃ₜ G n

/-- Milestone 3 (sub-pieces): smooth structures on G, UU, A. -/
theorem isOpen_G : IsOpen { g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0 }
theorem G_isOpenEmbedding :
    IsOpenEmbedding (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)

def UU.toNNHomeomorph : UU n ≃ₜ NN n                              -- via U ↦ U − 1
noncomputable def A.toFinNRHomeomorph : A n ≃ₜ (Fin n → ℝ)        -- via D ↦ (log D_{ii})_i

/-- Milestone 3 (Cayley transform on `K = O(n)`). -/
noncomputable def cayley : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
noncomputable def cayleyInv : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
theorem one_add_skew_isUnit (X : Sk n) : IsUnit ((1 + X.1).det)
theorem cayley_isOrthogonal (X : Sk n) : IsOrthogonal (cayley X.1)
noncomputable def cayleyToK : Sk n → K n
theorem cayley_self_inverse (X : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + X).det) : cayley (cayley X) = X
theorem cayleyInv_cayley (X : Sk n) : cayleyInv (cayley X.1) = X.1
theorem cayley_cayleyInv (Q : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (1 + Q).det) : cayley (cayleyInv Q) = Q
theorem cayleyInv_isSkew (Q : Matrix (Fin n) (Fin n) ℝ)
    (hOrth : IsOrthogonal Q) (h : IsUnit (1 + Q).det) :
    (cayleyInv Q).transpose = -(cayleyInv Q)
abbrev K_open (n : ℕ) : Type :=
    { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q ∧ IsUnit (1 + Q).det }
noncomputable def cayleyEquiv : (Sk n) ≃ K_open n
theorem continuous_cayley_on_skew : Continuous (fun X : Sk n => cayley X.1)
theorem continuous_cayleyInv_on_KOpen : Continuous (fun Q : K_open n => cayleyInv Q.1)
noncomputable def cayleyHomeomorph : (Sk n) ≃ₜ K_open n
noncomputable instance : ChartedSpace (Sk n) (K_open n)
instance : IsManifold (𝓘(ℝ, (Sk n : Type _))) ⊤ (K_open n)
noncomputable def cayleyDiffeomorph :
    Diffeomorph (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, (Sk n : Type _))) (Sk n) (K_open n) ⊤

/-- Multi-chart atlas: translated Cayley charts at every base point. -/
theorem IsOrthogonal.mul {Q R : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonal Q) (hR : IsOrthogonal R) : IsOrthogonal (Q * R)
abbrev K_open_at (Q₀ : K n) : Type
noncomputable def cayleyEquivAt (Q₀ : K n) : (Sk n) ≃ K_open_at Q₀
theorem self_mem_K_open_at (Q : K n) : IsUnit ((1 + Q.1 * Q.1.transpose).det)
noncomputable def cayleyOpenChartAt (Q₀ : K n) : OpenPartialHomeomorph (K n) (Sk n)
theorem cayleyOpenChartAt_source (Q₀ : K n) :
    (cayleyOpenChartAt Q₀).source =
      { Q : K n | IsUnit ((1 + Q.1 * Q₀.1.transpose).det) }
noncomputable instance instChartedSpaceK : ChartedSpace (Sk n) (K n)

/-- Milestone 4: Cartan Lie decomposition gl_n(ℝ) = Sym_n ⊕ Sk_n. -/
def Sym (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
def Sk  (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
theorem cartanLieDecomp (n : ℕ) : IsCompl (Sym n) (Sk n)

/-- Milestone 5: Iwasawa Lie subalgebras + direct-sum decomposition + linear iso. -/
def NN (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)   -- strict upper
def AA (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)   -- diagonal
abbrev KK (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) -- skew = Sk
theorem disjoint_AA_NN (n : ℕ) : Disjoint (AA n) (NN n)
theorem disjoint_KK_AA (n : ℕ) : Disjoint (KK n) (AA n)
theorem disjoint_KK_NN (n : ℕ) : Disjoint (KK n) (NN n)
theorem iwasawa_codisjoint (n : ℕ) : KK n ⊔ AA n ⊔ NN n = ⊤
theorem iwasawaLieDecomp (n : ℕ) :
    Disjoint (KK n) (AA n) ∧ Disjoint (KK n) (NN n) ∧ Disjoint (AA n) (NN n)
    ∧ KK n ⊔ AA n ⊔ NN n = ⊤
def iwasawaLieMap : (KK n × AA n × NN n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ
theorem iwasawaLieMap_surjective : Function.Surjective (iwasawaLieMap (n := n))
theorem iwasawaLieMap_injective  : Function.Injective  (iwasawaLieMap (n := n))
noncomputable def iwasawaLieEquiv :
    (KK n × AA n × NN n) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ

end IwasawaCoC
```

## Repository layout

```
iwasawa_change_of_coords/
├── README.md           this file
├── IwasawaCoC.lean     the main file (1666 lines)
└── AxiomCheck.lean     prints axiom dependencies of every named theorem
```

The project shares the parent's Lake build (single `lakefile.toml`,
single `lean-toolchain`, single Mathlib pin), so there is no duplicated
toolchain configuration.

## Build instructions

From `/Users/jiho/Desktop/math 157`:

```sh
lake build iwasawa_change_of_coords.IwasawaCoC
lake build iwasawa_change_of_coords.AxiomCheck   # prints axiom deps
```

The first build will compile the parent project's `project.Iwasawa`
as a dependency.

## Verifying the result

After a successful build, `AxiomCheck.lean` prints the axiom dependency
of every named theorem and instance in the file. All forty-six listed
items depend only on `[propext, Classical.choice, Quot.sound]` — i.e.,
exactly the three axioms used by classical Mathlib, with no
project-specific assumption and no `sorry`.

## Proof outlines

### Milestone 1 — Iwasawa bijection

The equivalence `iwasawaEquiv : K × A × UU ≃ G` reuses the parent
project's existence (`Iwasawa.exists_iwasawa`) and uniqueness
(`Iwasawa.iwasawa_unique`).

* Forward: `(k, a, u) ↦ ⟨k · a · u, _⟩`, with `det (kau) ≠ 0` from the
  three component invertibility lemmas.
* Backward: take the Iwasawa factorization `F := Iwasawa.iwasawa g.2`
  and return its `(k, a, u)`-components as subtypes.
* `right_inv` is `F.factorization.symm`.
* `left_inv` builds an explicit `IwasawaFactorization (kau)` from
  `(k, a, u)` and applies `Iwasawa.iwasawa_unique`.

### Milestone 1b — Convention swap and Cartan involution

`inv_iwasawa_jl` is a direct algebraic identity:

```
(k · a · u)⁻¹ = u⁻¹ · (k · a)⁻¹                  (Matrix.mul_inv_rev)
              = u⁻¹ · a⁻¹ · k⁻¹                  (Matrix.mul_inv_rev, mul_assoc)
              = u⁻¹ · a⁻¹ · kᵀ                   (IsOrthogonal.matInv_eq_transpose)
```

`cartanInvolution g := ⟨(g.1)ᵀ⁻¹, _⟩` requires showing
`((g.1)ᵀ⁻¹).det ≠ 0`, which follows from
`g.1.transpose * (g.1.transpose)⁻¹ = 1` via `Matrix.mul_nonsing_inv` and
taking determinants.

`cartanInvolution_involutive` reduces to
`(((g.1)ᵀ)⁻¹)ᵀ⁻¹ = g.1` via the rewrite chain
`Matrix.transpose_nonsing_inv → Matrix.transpose_transpose →
Matrix.nonsing_inv_nonsing_inv`.

### Milestone 2 — Topology and Gram–Schmidt continuity

`continuous_iwasawaMap` is one rule of `Continuous.matrix_mul` lifted
through subtype embeddings.

`continuous_iwasawaSymm` is the substantial piece. It reduces to
continuity of the parent project's Gram–Schmidt-derived `qMat`, `dMat`,
`uMat` on `G n`, which in turn reduces to continuity of `gramSchmidt`
and `gramSchmidtNormed` (Mathlib's
`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`) in the input
function, on the locus of linearly-independent column families.
Mathlib v4.30 does not package this continuity, so we prove it inline:

* `continuous_gCol_at` — column extraction is continuous.
* `continuous_gramSchmidt_at` — by well-founded induction on `i : Fin n`.
  Inductive step: rewrite via `gramSchmidt_def` to
  `gCol g.1 i − ∑ j ∈ Iio i, (ℝ ∙ gramSchmidt _ j).starProjection (gCol _ i)`.
  The 1D projection becomes the rational expression
  `(⟨v, w⟩ / ‖v‖²) • v` via `Submodule.starProjection_singleton`, which
  is continuous because the denominator is nonzero on `G n`
  (`gramSchmidt_ne_zero` applied to `Iwasawa.gCol_linearIndependent`).
* `continuous_gramSchmidtNormed_at` — division by nonzero norm.
* `continuous_qMat_subtype`, `continuous_rMat_subtype`,
  `continuous_dMat_subtype`, `continuous_diagInv_dMat_subtype`,
  `continuous_uMat_subtype` — entry-wise continuity of the four matrix
  factors built from Gram–Schmidt outputs.
* `continuous_iwasawaSymm` assembles the three factors.

This is the kind of result that could plausibly be upstreamed to
Mathlib (continuity of `gramSchmidt` and `gramSchmidtNormed` in their
input function, on the linearly-independent locus); see
`Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho` as the natural
home.

### Milestone 3 — Smooth structures

Open-submanifold smoothness on `G n` is direct: `G n` is open in
`Matrix (Fin n) (Fin n) ℝ` (preimage of `≠ 0` under continuous `det`),
so `IsOpenEmbedding.singletonChartedSpace` and
`IsOpenEmbedding.isManifold_singleton` apply. The norm on Matrix is
chosen via `attribute [local instance]` over
`Matrix.normedAddCommGroup` and `Matrix.normedSpace` (Mathlib
intentionally does not register a global matrix norm because several
natural choices exist).

`UU n` is modeled on `NN n` (the strictly upper-triangular `Submodule`)
via the homeomorphism `UU.toNNHomeomorph U := U − 1`. The chart is
single (covers all of `UU n`) and gives `ChartedSpace` and `IsManifold`
instances via `OpenPartialHomeomorph.singletonChartedSpace`.

`A n` is modeled on `Fin n → ℝ` via `A.toFinNRHomeomorph D := (log D_{ii})_i`
with inverse `v ↦ diag(exp v)`, giving a single-chart smooth structure.

### Milestone 3 — Cayley transform on `O(n)`

The major mathematical work. The Cayley transform

```
cayley X = (1 − X)(1 + X)⁻¹
```

provides a parametrization of `O(n)` minus a measure-zero set by
skew-symmetric matrices. The full chain:

* `one_add_skew_isUnit` (`1 + X` invertible for `X` skew). Proof:
  `(1 + X)(1 − X) = 1 + X · Xᵀ` (using `Xᵀ = −X`), and
  `1 + X · Xᵀ` is positive definite (`1` is `PosDef`, `X · Xᵀ` is
  `PosSemidef` via `posSemidef_self_mul_conjTranspose`). Hence
  `(1 + X)(1 − X)` is a unit, so `1 + X` is too (via
  `isUnit_of_mul_isUnit_left`).
* `cayley_isOrthogonal` — `(cayley X)(cayley X)ᵀ = 1` for `X` skew, by
  algebraic manipulation using the commutativity of `(1 + X)` and
  `(1 − X)` (and their inverses).
* `cayley_self_inverse` — for any `X` with `1 + X` invertible,
  `cayley(cayley X) = X`. The proof shows
  `1 − cayley X = X · (1 + cayley X)` by post-multiplying both sides by
  `(1 + X)` and using the algebraic identities
  `(1 ± cayley X)(1 + X) = X + X` and `(1 + cayley X)(1 + X) = 1 + 1`.
  Specializations give the left/right inverses
  `cayleyInv_cayley` (on `Sk n`) and `cayley_cayleyInv` (on the
  invertibility set).
* `cayleyInv_isSkew` — for orthogonal `Q` with `1 + Q` invertible,
  `cayleyInv Q` is skew-symmetric. The proof uses
  `Qᵀ = Q⁻¹` (orthogonality) plus the identity
  `(1 + Q⁻¹) = Q⁻¹ · (1 + Q)`, the commutativity of polynomials in `Q`,
  and direct computation of the transpose.
* `cayleyEquiv : Sk n ≃ K_open n` bundles the bijection.
* `continuous_cayley_on_skew` and `continuous_cayleyInv_on_KOpen` use
  Mathlib's `continuousAt_matrix_inv` (for the matrix inverse) and
  `NormedRing.inverse_continuousAt` (for `Ring.inverse` on units).
* `cayleyHomeomorph` bundles topological bijection.
* `instChartedSpaceKOpen`, `instIsManifoldKOpen` — `K_open n` is a
  smooth manifold modeled on `Sk n` via the Cayley chart, set up using
  `IsOpenEmbedding.singletonChartedSpace` on `cayleyHomeomorph.symm`.
* `contMDiff_cayleyHomeomorph`, `contMDiff_cayleyHomeomorphSymm` —
  smoothness in both directions, using `contMDiff_isOpenEmbedding` and
  `contMDiffOn_isOpenEmbedding_symm` plus the function-equality
  identification of `cayleyHomeomorph` with the
  `OpenPartialHomeomorph`-inverse via
  `IsOpenEmbedding.toOpenPartialHomeomorph_left_inv`.
* `cayleyDiffeomorph` is the bundled `C∞` diffeomorphism.

### Milestone 3 — Multi-chart atlas (Sphere pattern)

The single Cayley chart at the identity covers `K_open n` (the open
dense subset of `O(n)` where `−1` is not an eigenvalue of `Q`). To
cover the rest of `O(n)`, we follow Mathlib's pattern from
[`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html)
(stereographic projection from each unit vector — Heather Macbeth,
2021) and put a chart at every point.

* `IsOrthogonal.mul` — group closure of `K`.
* `K_open_at Q₀` — translated open subset
  `{ Q ∈ K | (1 + Q · Q₀ᵀ).det.IsUnit }`.
* `cayleyEquivAt Q₀ : Sk n ≃ K_open_at Q₀` — set-level bijection,
  proved by reduction to the identity-centered case using
  `cayleyEquiv.symm` and right-multiplication by `Q₀`/`Q₀ᵀ`.
* `self_mem_K_open_at` — for any `Q ∈ K n`, `Q ∈ K_open_at Q` (since
  `Q · Qᵀ = 1` and `1 + 1` has invertible determinant `2ⁿ`).
* `cayleyOpenChartAt Q₀` — bundles each translated equivalence as an
  `OpenPartialHomeomorph (K n) (Sk n)`. The construction goes through
  `(cayleySourceAt Q₀).openPartialHomeomorphSubtypeCoe.symm.trans
  cayleyChartHomeomorphAt Q₀.toOpenPartialHomeomorph`, avoiding the
  if-then-else / decidability issues that arise if one tries to define
  the chart's `toFun` globally.
* `instChartedSpaceK` — full atlas on `K n`, with one translated
  Cayley chart at each point.

### Milestone 4 — Cartan Lie decomposition

`IsCompl (Sym n) (Sk n)` splits into

* *Disjoint*: `M ∈ Sym ∩ Sk` ⟹ `Mᵀ = M = −M` ⟹ `2 · M = 0` ⟹ `M = 0`.
* *Codisjoint*: `M = ½(M + Mᵀ) + ½(M − Mᵀ)`.

### Milestone 5 — Iwasawa Lie decomposition

Pairwise disjoint:
* `disjoint_AA_NN` — diagonal ∩ strictly upper = 0.
* `disjoint_KK_AA` — skew-symmetric diagonal forces all entries zero.
* `disjoint_KK_NN` — case split below/diagonal/above.

`iwasawa_codisjoint` (`𝔨 ⊔ 𝔞 ⊔ 𝔫 = ⊤`) is the explicit decomposition

```
M = K + A + N
A_{ij} = M_{ii}      if i = j, else 0   (in 𝔞)
K_{ij} = M_{ij}      if j < i           (in 𝔨, skew-symmetrized)
       = -M_{ji}     if i < j
       = 0           if i = j
N_{ij} = M_{ij} + M_{ji}  if i < j      (in 𝔫, strict upper)
       = 0                otherwise
```

Verification is entry-by-entry on the trichotomy
`j < i / i = j / i < j`.

`iwasawaLieDecomp` bundles the four conditions.

`iwasawaLieMap`/`iwasawaLieEquiv` is the linear sum map
`(X, Y, Z) ∈ 𝔨 × 𝔞 × 𝔫 ↦ X + Y + Z`. Surjectivity is
`iwasawa_codisjoint`. Injectivity is the entry-wise argument:

* `j < i`: `Y_{ij} = 0` (off-diag), `Z_{ij} = 0` (`j ≤ i`), so `X_{ij} = 0`.
* `j = i`: `X_{ii} = −X_{ii}` (skew) gives `X_{ii} = 0`; same for `Y`, `Z`.
* `i < j`: by the previous case at `(j, i)` we have `X_{ji} = 0`; skew
  gives `X_{ij} = −X_{ji} = 0`, then `Y_{ij} = 0` (off-diag), `Z_{ij} = 0`.

This is the algebraic content of "the differential of the Iwasawa map
at the identity is invertible," realized as a `LinearEquiv`.

## Remaining work

Three pieces are not closed in this file:

### 1. `instIsManifoldK` — chart-transition `ContDiffOn`

The chart compatibility for the multi-chart atlas. After
`isManifold_of_contDiffOn` reduces it to a `ContDiffOn` statement, the
remaining content is the smoothness of the transition

```
X ∈ Sk n ↦ cayleyInv ((cayley X · Q₀.1) · Q₁.1.transpose)
```

on the open set

```
{ X : Sk n | IsUnit ((1 + (cayley X · Q₀.1) · Q₁.1.transpose).det) }.
```

This decomposes through:

* `ContDiff ℝ ⊤ (cayley : Sk n → Matrix _ _ ℝ)` — Cayley as a rational
  expression with non-vanishing denominator on `Sk n`. Each piece is
  `ContDiff` (linear maps for `1 ± X`, `contDiffAt_ringInverse` for
  inversion on units).
* `ContDiff ℝ ⊤ (· * R)` for fixed orthogonal `R` — linear, hence
  smooth (`ContinuousLinearMap.contDiff` or the bilinear-map lemma
  `isBoundedBilinearMap_apply.contDiff`).
* `ContDiffOn ℝ ⊤ cayleyInv {M | (1+M).det.IsUnit}` — same shape as
  the cayley `ContDiff`.

The composition is `ContDiffOn` on the relevant open set, with
`ContDiffOn.comp` and `ContDiffOn.congr` to massage the set definitions
to align with Mathlib's abstract `(e.symm ≫ₕ e').source`.

We have the file documented with the precise structure of the proof
at the end of the `CayleyTransform` section. Closing this one item
gives `instIsManifoldK`.

### 2. `iwasawaDiffeomorph : K × A × U ≃ₘ GL_n(ℝ)`

Once `instIsManifoldK` is in place, this is an assembly of
`iwasawaEquiv` (set-theoretic), forward smoothness (matrix
multiplication is `ContMDiff` on a normed algebra), and inverse
smoothness (a `C∞` upgrade of `continuous_iwasawaSymm` using
`ContDiff` of Gram–Schmidt — the same inductive proof structure as
the continuity proof we already gave, lifted to the smooth category).
Approximately 80–150 more lines.

### 3. `iwasawaMap_mfderiv_at_one` — geometric `mfderiv` at the identity

Showing the differential of `iwasawaMap` at `(1, 1, 1)` equals the
linear sum map `(X, Y, Z) ↦ X + Y + Z` realized by `iwasawaLieEquiv`.
The proof uses `mfderiv_eq_fderiv` (when manifolds are themselves
normed spaces, `mfderiv` reduces to `fderiv`), plus a direct Jacobian
computation of the Cayley chart at `0 ∈ Sk` (the first-order Taylor
expansion of `cayley` at `0` is `X ↦ 1 + 2X + O(X²)`, so the
differential of `cayleyHomeomorph` at `0` is multiplication by `2`,
which is invertible). Approximately 100 lines.

## Why this is the natural stopping point for us

The three remaining pieces are concrete Mathlib pattern work, not
research gaps. The mathematical content — every Cayley algebraic
identity, every continuity proof, every set-theoretic equivalence,
the Iwasawa Lie decomposition, the linear-algebra differential — is
proved and axiom-clean. What we lack is the deep working fluency with
Mathlib's `ContDiff` / `ContMDiff` / `isManifold_of_contDiffOn` /
`ModelWithCorners` machinery to close out the smoothness composition
proof reliably. Each of our attempts either introduced `sorry`s
(rejected by Mathlib's warnings-as-errors build policy) or got tangled
in idiomatic typeclass juggling.

We believe the cleanest next step — substantially more useful than
finishing inside this one file — is an upstream Mathlib contribution
adding `O(n)` (or more generally the orthogonal/unitary group of a
finite-dimensional real/complex inner product space) as a smooth Lie
subgroup of `GL_n` via the Cayley-transform atlas, paralleling the
existing `Mathlib.Geometry.Manifold.Instances.Sphere`. The Cayley-side
groundwork in this file (`cayley`, `cayleyInv`, `one_add_skew_isUnit`,
`cayley_isOrthogonal`, `cayley_self_inverse`, `cayleyInv_isSkew`,
`cayleyEquiv`, `cayleyHomeomorph`, `cayleyDiffeomorph` on the
identity-centered chart, and `cayleyEquivAt` plus `cayleyOpenChartAt`
for the translated charts) is structured to be liftable to such a
Mathlib PR with relatively little adaptation.

## References

- J. Jorgenson, S. Lang. *Spherical Inversion on `SL_n(R)`*. Springer
  Monographs in Mathematics, 2001. (Primary source — Chapter I, §1–§3.)
- S. Lang. *Linear Algebra*, 3rd edition. Springer Undergraduate Texts
  in Mathematics, 1987. (Convention for the parent project.)
- A. Cayley. "Sur quelques propriétés des déterminants gauches."
  *Crelle's Journal* 32 (1846), 119–123.
- The Mathlib community.
  [Mathlib4](https://github.com/leanprover-community/mathlib4).
- H. Macbeth. [`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html), 2021.
  (Stereographic projection multi-chart atlas — the model we follow
  for `cayleyOpenChartAt`.)
- [`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html) — transpose / inverse interaction.
- [`Mathlib.LinearAlgebra.Matrix.PosDef`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html) — `PosDef.add_posSemidef`, `PosDef.isUnit`, `posSemidef_self_mul_conjTranspose` (used in `one_add_skew_isUnit`).
- [`Mathlib.Analysis.Matrix.Normed`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Normed.html) — locally-attributed matrix norm.
- [`Mathlib.Topology.Instances.Matrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/Matrix.html) — continuity of matrix operations, including `continuousAt_matrix_inv` (used in `continuous_cayley_on_skew` / `continuous_cayleyInv_on_KOpen`).
- [`Mathlib.Geometry.Manifold.IsManifold.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold/Basic.html) — `IsOpenEmbedding.isManifold_singleton`, `isManifold_of_contDiffOn`.
- [`Mathlib.Geometry.Manifold.Diffeomorph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Diffeomorph.html) — `Diffeomorph` structure.

## License

Released for educational and academic use.

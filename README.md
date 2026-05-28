# Iwasawa Decomposition and Change of Coordinates

A Lean 4 / Mathlib formalization of **Theorem 1.1** of

> J. Jorgenson, S. Lang. *Spherical Inversion on* $`SL_n(\mathbb{R})`$.
> Springer Monographs in Mathematics, 2001.

The Iwasawa product map

```math
\Phi : K \times A \times U \to GL_n(\mathbb{R}), \qquad (k, a, u) \mapsto k \cdot a \cdot u
```

is asserted by Jorgenson and Lang to be a *differential isomorphism*
(diffeomorphism), where

- $`K = O(n)`$ is the real orthogonal group,
- $`A`$ is the group of positive diagonal $`n \times n`$ real matrices,
- $`U`$ is the group of unipotent upper triangular $`n \times n`$ real matrices.

This project formalizes the algebraic, topological, and smooth
content of that theorem, building on top of the parent project's
[`project.Iwasawa`](../project/Iwasawa.lean), which provides the
set theoretic existence and uniqueness of the Iwasawa factorization
following Lang's *Linear Algebra*.

## Status at a glance

| Quantity | Value |
|---|---|
| Build status | `lake build` succeeds |
| Active Lean `sorry` declarations in `iwasawa_change_of_coords/` | 0 |
| Core algebraic, topological, smooth, and Jacobian axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Quarantined future axiom | 1 explicit Haar / change-of-variables bridge axiom in `IwasawaBridge.lean` |

The following layers are closed, with no `sorry`, and each prints only the
standard Lean and Mathlib axioms `[propext, Classical.choice, Quot.sound]`:

- the set-theoretic Iwasawa equivalence and the homeomorphism;
- the full smooth structure on $`K = O(n)`$ (`instIsManifoldK`) via the
  translated multi-chart Cayley atlas, and the full diffeomorphism
  `iwasawaDiffeomorph`;
- the manifold differential of the product map at the identity
  (`iwasawaMfderivAtIdentity`) and at a general point
  (`iwasawaMfderivAtFactored`);
- the closed-form Jacobian determinant of the charted Iwasawa map in the
  Iwasawa bases, at a general point of the chart domain
  (`detInIwasawaBases_fderiv_iwasawaCharted_general` and its absolute-value
  form), resting on the Sylvester-Franke identity
  $`\det\bigl(\Lambda^2 B\bigr) = (\det B)^{\,n-1}`$ (`det_sandwichOnSkCLM`).

A single consolidated file, `IwasawaComplete.lean`, restates every main result
with a clean signature and prints its axiom dependencies. The repository should
not be described as axiom-free without qualification: `IwasawaBridge.lean`
still contains one explicit future-facing axiom for the Haar measure
pushforward, which is the only step not yet reduced to the standard three
axioms.

## Current scope boundary

The proved core now includes the Iwasawa equivalence, the homeomorphism, the
full diffeomorphism, the smooth forward and inverse maps, the manifold
differential of the product map, and the explicit Jacobian determinant of the
charted map in the Iwasawa source basis and the standard matrix target basis.
The derivative uses the project's chart convention: `iwasawaMatrixLeibnizCLM`
is the differential of `iwasawaMap` in the Cayley, logarithm, and affine
charts, and `iwasawaCharted` is the corresponding single-chart flat map

```math
(X, v, Z) \mapsto \mathrm{cayley}(X)\, \mathrm{diag}(e^{v})\, (Z + 1).
```

The one remaining layer is the Haar measure pushforward itself: turning the
pointwise Jacobian determinant into a measure-theoretic change-of-variables
identity for product Haar measures. This is recorded as a single quarantined
axiom in `IwasawaBridge.lean` and is the subject of [Remaining Work](#remaining-work).
The positive-root product

```math
\delta(a) = \prod_{i \lt j} \frac{a_i}{a_j}
```

is computed by `adNN_det_eq_pair_product` as the determinant of $`\mathrm{Ad}(a)`$
on the strictly-upper subalgebra, and now appears inside the proved Jacobian
determinant rather than only as an isolated ingredient.

## Provenance and convention

The parent project follows Lang's *Linear Algebra* (3rd edition, 1987)
and writes the Iwasawa decomposition as $`g = k \cdot a \cdot u`$ (orthogonal,
positive diagonal, upper unipotent, with $`K`$ on the *left*).

Jorgenson and Lang use the opposite order $`g = u \cdot a \cdot k`$ ($`K`$ on the
*right*). The clean change of coordinates between the two conventions
is **inversion**: if $`g = k \cdot a \cdot u`$ (Lang), then

```math
g^{-1} = u^{-1} \cdot a^{-1} \cdot k^{T}
```

is in the Jorgenson and Lang form (upper unipotent, then positive diagonal,
then orthogonal),
since the inverse of an upper unipotent matrix is upper unipotent, the
inverse of a positive diagonal matrix is positive diagonal, and the
transpose of an orthogonal matrix is orthogonal.

The Cartan involution $`\theta : g \mapsto (g^T)^{-1}`$ is a separate involution that
Jorgenson and Lang use on p. 2 to characterize $`K`$ as its fixed point subgroup. We
formalize both.

## Mathematical motivation: why the Iwasawa decomposition is a change of coordinates

### From decomposition to coordinates

$`GL_n(\mathbb{R})`$ is an open subset of the $`n^2`$ dimensional matrix space
$`\mathrm{Mat}_n(\mathbb{R})`$, so as a manifold it is $`n^2`$ dimensional. The three
subgroups in the Iwasawa decomposition contribute exactly the right
dimensions to add up to $`n^2`$:

```math
\dim K = \dim O(n) = \frac{n(n-1)}{2} \quad \text{(skew symmetric matrices)}
```

```math
\dim A = \dim \{\text{positive diagonals}\} = n \quad \text{(one positive real per diagonal entry)}
```

```math
\dim U = \dim \{\text{upper unipotent}\} = \frac{n(n-1)}{2} \quad \text{(strictly upper entries)}
```

```math
\dim K + \dim A + \dim U = \frac{n(n-1)}{2} + n + \frac{n(n-1)}{2} = n^2.
```

The product map

```math
\Phi : K \times A \times U \to GL_n(\mathbb{R}), \qquad \Phi(k, a, u) = k \cdot a \cdot u
```

is therefore a map between two manifolds of equal dimension. The
content of Theorem 1.1 is that $`\Phi`$ is not merely a bijection but a
*differential isomorphism* (diffeomorphism). What this **really
means** is that $`(k, a, u)`$ is a **system of global coordinates**
on $`GL_n(\mathbb{R})`$, or equivalently, that the Iwasawa decomposition
gives a *change of coordinates* from the ambient matrix entries
$`(g_{ij})`$ to the triple $`(k, a, u)`$.

This is more than a curiosity. The Iwasawa coordinates are far
better adapted to the structure of the group than the ambient
entries: $`K`$ carries a compact Lie group structure, $`A`$ is a free
abelian group $`(\mathbb{R}^+)^n`$, and $`U`$ is a unipotent group on which the
exponential map is a *polynomial* diffeomorphism with the Lie
algebra of strictly upper triangular matrices. Many constructions
in representation theory, harmonic analysis on Lie groups, and
spherical function theory either *cannot* or are dramatically
harder to express in the ambient $`(g_{ij})`$ coordinates and become
natural in the Iwasawa coordinates.

### The Jacobian bridge: invariant measure transforms by the Iwasawa character

The classical bridge between "Iwasawa decomposition" and
"change of coordinates Jacobian" is the **Haar measure
decomposition formula**. If $`dx`$ is a (left) Haar measure on
$`G = GL_n(\mathbb{R})`$, with $`du`$, $`da`$, $`dk`$ Haar measures on $`U`$, $`A`$, $`K`$,
and the product map $`U \times A \times K \to UAK = G`$ is the Jorgenson and Lang Iwasawa map,
then for any $`f \in C_c(G)`$

```math
\int_G f(x)\, dx = c \cdot \int_U \int_A \int_K f(uak) \cdot \delta(a)^{-1}\, du\, da\, dk
```

for a constant $`c`$ and a homomorphism $`\delta : A \to \mathbb{R}^+`$ called the
**Iwasawa character** (Jorgenson and Lang, Propositions 2.1, 2.3, 2.4). The
Jacobian factor is precisely $`\delta(a)^{-1}`$: changing variables from
$`x \in G`$ to $`(u, a, k) \in U \times A \times K`$ introduces the determinant of
the differential of the Iwasawa map, which equals $`\delta(a)`$ (up to the
constant $`c`$).

For $`G = GL_n(\mathbb{R})`$ with the standard upper unipotent, positive diagonal, and
orthogonal Iwasawa data, the explicit formula in Equation (3) of §I.2 of
Jorgenson and Lang reads

```math
\delta(a) = \prod_{i \lt j} \frac{a_i}{a_j} = \prod_{i=1}^{n} a_i^{n - 2i + 1}.
```

This is the **explicit Jacobian** of the change of coordinates from
ambient matrix entries to Iwasawa coordinates $`(u, a, k)`$. The
proof is a direct computation: $`\delta(a)`$ is the determinant of the
conjugation action of $`a \in A`$ on the Lie algebra $`\mathfrak{n} = \mathrm{Lie}(U)`$ of
strictly upper triangular matrices, because the Lie algebra $`\mathfrak{n}`$
is the *tangent space* to $`U`$ at the identity, and the change of
variable formula on a Lie group near a point is governed by the
adjoint action on the Lie algebra (Equations (1) through (3) of §I.2 of Jorgenson and Lang).
The eigenvalues of $`\mathrm{Ad}(a)`$ on the basis $`E_{ij}`$ (for $`i \lt j`$) of $`\mathfrak{n}`$
are exactly the characters $`\chi_{ij}(a) = a_i / a_j`$, and $`\delta(a)`$ is
the product of these.

This $`\mathrm{Ad}(a)`$ determinant is `adNN_det_eq_pair_product` in the project,
and it is now a *factor* of the fully formalized pointwise Jacobian
determinant of the charted Iwasawa map
(`absDetInIwasawaBases_fderiv_iwasawaCharted_general`). What is not yet
formalized is the last step, integrating this density against Haar measure to
obtain the displayed integration formula; that step is the single quarantined
axiom in `IwasawaBridge.lean`.

### Why a *differential* isomorphism (not just a bijection)

A bijection just renames points: it lets you say "every $`g`$ has a
unique $`(k, a, u)`$". A homeomorphism additionally guarantees that
the renaming is continuous in both directions: convergence of $`g_n`$
to $`g`$ translates to convergence of $`(k_n, a_n, u_n)`$ to $`(k, a, u)`$.
A *diffeomorphism* additionally guarantees that the renaming is
**smooth in both directions**: derivatives, vector fields, and
integrals all transform correctly under the change of coordinates.

For our purposes, only the diffeomorphism level is strong enough to
support the Haar measure decomposition formula: the Jacobian of a
change of coordinates is the absolute value of the determinant of
the differential of the change, so without a *differential*
isomorphism we cannot even *state* the Jacobian formula. This is
why Theorem 1.1 of Jorgenson and Lang asserts a **differential**
isomorphism, and why our project's central technical content is
the smooth manifold story (the Cayley transform giving a
diffeomorphism $`\mathrm{Sk}\,n \simeq K_{\mathrm{open}}\,n`$, and the Sphere pattern multi chart
atlas covering all of $`K = O(n)`$).

### Connection to the Lie algebra: infinitesimal change of coordinates

Every smooth change of coordinates on a Lie group induces an
**infinitesimal change of coordinates** at the identity, namely a
linear isomorphism between Lie algebras. For the Iwasawa map
$`\Phi : K \times A \times U \to G`$, the differential at the identity
$`(1, 1, 1) \in K \times A \times U`$ is a linear map

```math
d\Phi_{(1,1,1)} : \mathfrak{k} \times \mathfrak{a} \times \mathfrak{n} \to \mathfrak{gl}_n(\mathbb{R}), \qquad (X, Y, Z) \mapsto X + Y + Z
```

where $`\mathfrak{k} = \mathrm{Lie}(K) = \{\text{skew symmetric matrices}\} = \mathrm{Sk}_n`$,
$`\mathfrak{a} = \mathrm{Lie}(A) = \{\text{real diagonal matrices}\}`$, and
$`\mathfrak{n} = \mathrm{Lie}(U) = \{\text{strictly upper triangular matrices}\}`$.

For $`d\Phi_{(1,1,1)}`$ to be a linear isomorphism, the three subspaces
$`\mathfrak{k}, \mathfrak{a}, \mathfrak{n}`$ must form a **direct sum decomposition** of $`\mathfrak{gl}_n(\mathbb{R})`$.
This is the **Iwasawa Lie decomposition**:

```math
\mathfrak{gl}_n(\mathbb{R}) = \mathfrak{k} \oplus \mathfrak{a} \oplus \mathfrak{n}.
```

This is the *purely linear algebraic shadow* of Theorem 1.1, and
has the same dimension count, $`n(n-1)/2 + n + n(n-1)/2 = n^2`$, and
the same role: it expresses every matrix as a sum of a skew, a
diagonal, and a strictly upper triangular piece in a unique way.
The decomposition is also the natural setting for the structure
theory of semisimple Lie algebras (root spaces, parabolic
subalgebras, Borel subalgebras, etc.).

The closely related **Cartan Lie decomposition** is the coarser
splitting

```math
\mathfrak{gl}_n(\mathbb{R}) = \mathrm{Sym}_n \oplus \mathrm{Sk}_n
```

into symmetric and skew symmetric parts. The Iwasawa decomposition
*refines* the symmetric component using the symmetrization of the strictly
upper triangular subalgebra (§I.3, p. 14 of Jorgenson and Lang):

```math
\mathfrak{a} \oplus \mathfrak{n}_{\mathrm{sym}}, \qquad \mathfrak{n}_{\mathrm{sym}} = \tfrac{1}{2}(\mathfrak{n} + \mathfrak{n}^T).
```

In this project we prove both the Iwasawa Lie decomposition
(`iwasawaLieDecomp` and `iwasawaLieEquiv`) and the Cartan Lie
decomposition (`cartanLieDecomp`). The geometric statement that
$`d\Phi_{(1,1,1)}`$ is the linear sum map is the content of
`iwasawaMfderivAtIdentity`, which is now proved. The algebraic
input is that *the candidate linear map* $`(X, Y, Z) \mapsto X + Y + Z`$
is a `LinearEquiv`; the geometric statement follows from the smooth
manifold structure on the full $`K = O(n)`$ together with the first-order
Taylor expansion of the Cayley chart at $`0 \in \mathrm{Sk}`$, namely
$`\mathrm{cayley}(X) = 1 - 2X + O(X^2)`$ (so the Cayley chart contributes a
factor of $`-2`$ on the $`K`$-direction).

## The mathematics formalized in this project

The remainder of this section walks through every theorem,
definition, and instance in the file in mathematical detail, in
the order they appear in `IwasawaCoC.lean`. (See [Theorem
statements](#theorem-statements) below for the exact Lean
signatures, and [Proof outlines](#proof-outlines) for the
proof level summaries.)

### 1. The Iwasawa decomposition: $`K \times A \times U \simeq GL_n(\mathbb{R})`$

The starting point. Every invertible real $`n \times n`$ matrix $`g`$ admits
a unique factorization

```math
g = k \cdot a \cdot u, \qquad k \in O(n),\ a \text{ positive diagonal},\ u \text{ upper unipotent}.
```

The proof goes through Gram, Schmidt orthonormalization: write $`g`$'s
columns as a tuple of vectors $`(v_1, \ldots, v_n)`$, run the Gram, Schmidt
procedure to produce an orthonormal basis $`(e_1', \ldots, e_n')`$ of $`\mathbb{R}^n`$,
let $`Q`$ be the matrix of $`e_i'`$ (orthogonal), and $`R = Q^T g`$ (upper
triangular with positive diagonal). Then $`R = a \cdot u`$ for $`a`$ the
diagonal of $`R`$ and $`u = a^{-1} R`$ upper unipotent. Set $`k = Q`$.

Uniqueness comes from a clever orthogonality argument: an
orthogonal upper triangular matrix with positive diagonal must be
the identity. This existence plus uniqueness is the parent project
[`project.Iwasawa`](../project/Iwasawa.lean), which we wrap as
`iwasawaEquiv : K n × A n × UU n ≃ G n`, encoding the bijection
$`K \times A \times U \simeq GL_n(\mathbb{R})`$.

The mathematical content "Iwasawa decomposition is QR
decomposition" should be appreciated here: in numerical linear
algebra parlance this *is* the QR factorization, and the
Iwasawa coordinate Jacobian formula above is the Jacobian of QR
in disguise.

### 2. Convention swap (Lang vs Jorgenson and Lang) and the Cartan involution

The convention swap is a useful exercise in matrix algebra. Lang
writes $`g = k \cdot a \cdot u`$. Jorgenson and Lang write $`g = u \cdot a \cdot k`$. These are *not*
related by simply re labeling factors of the *same* $`g`$: they are
two different factorizations.

The connection is **inversion**: if $`g = kau`$ in Lang form, then
taking inverses

```math
g^{-1} = u^{-1} \cdot a^{-1} \cdot k^{-1} = u^{-1} \cdot a^{-1} \cdot k^{T}
```

(using $`k^{-1} = k^T`$ for orthogonal $`k`$). The right hand side is in
the Jorgenson and Lang form, since:

* $`u^{-1}`$ is upper unipotent (the inverse of an upper unipotent
  matrix is upper unipotent, an easy proof by induction on $`n`$ or by
  explicitly truncating the geometric series),
* $`a^{-1}`$ is positive diagonal (diagonal entries $`1/a_i \gt 0`$),
* $`k^T`$ is orthogonal ($`k^T \cdot (k^T)^T = k^T k = 1`$).

So **inversion** is the change of coordinates between Lang's $`g`$
and the Jorgenson and Lang $`g^{-1}`$. This is `inv_iwasawa_jl`.

The **Cartan involution** is a *different* operation:

```math
\theta : GL_n(\mathbb{R}) \to GL_n(\mathbb{R}), \qquad \theta(g) = (g^T)^{-1} = (g^{-1})^T.
```

It is an order 2 group automorphism (`cartanInvolution_involutive`).
Jorgenson and Lang use it on p. 2 to characterize the orthogonal subgroup as its
fixed point set:

```math
K = \{ g \in GL_n(\mathbb{R}) \mid \theta(g) = g \} = \{ g \mid (g^T)^{-1} = g \} = \{ g \mid g \cdot g^T = 1 \}
```

which is exactly the orthogonality condition. The Cartan involution
also induces an involution on the Lie algebra $`\mathfrak{gl}_n(\mathbb{R})`$ whose
fixed point set is $`\mathfrak{k} = \mathrm{Sk}_n`$ and whose $`-1`$ eigenspace is $`\mathfrak{p} = \mathrm{Sym}_n`$,
giving the **Cartan Lie decomposition** $`\mathfrak{gl}_n = \mathfrak{k} \oplus \mathfrak{p}`$ of Milestone 4.

### 3. Topology: the Iwasawa map is a homeomorphism

The forward direction of continuity is straightforward: matrix
multiplication $`(k, a, u) \mapsto k \cdot a \cdot u`$ is jointly continuous (a
finite product of bilinear matrix multiplication operations,
each of which is continuous by `Continuous.matrix_mul`), and we
embed the result back into the open subtype $`GL_n(\mathbb{R})`$ via
`Continuous.subtype_mk`. This gives `continuous_iwasawaMap`.

The inverse direction is substantially harder, and is the most
technically interesting topological content of the project. Given
$`g \in GL_n(\mathbb{R})`$, we need to show that the maps $`g \mapsto k`$, $`g \mapsto a`$,
$`g \mapsto u`$ are continuous. Each of these is built from Gram, Schmidt
orthonormalization applied to the columns of $`g`$, so we are
asking: **is Gram, Schmidt continuous in its input function?**

The answer is yes, on the open set of input tuples that are
linearly independent. The intuition: the Gram, Schmidt outputs are
rational functions of the input vectors, with positive denominators
(norms of intermediate vectors) on the linearly independent locus,
so they are continuous (in fact smooth). Concretely, Wikipedia's
"Gram, Schmidt process" article gives an explicit determinantal
formula:

```math
u_j = \frac{1}{D_{j-1}} \det \begin{pmatrix} \langle v_1, v_1 \rangle & \langle v_2, v_1 \rangle & \cdots & \langle v_j, v_1 \rangle \\ \vdots & \vdots & \ddots & \vdots \\ \langle v_1, v_{j-1} \rangle & \cdots & \cdots & \langle v_j, v_{j-1} \rangle \\ v_1 & v_2 & \cdots & v_j \end{pmatrix}
```

where $`D_{j-1}`$ is the Gram determinant of the previous vectors.
Since each entry is a polynomial in the $`v_i`$ and $`D_{j-1} \gt 0`$
on the linearly independent locus, each $`u_j`$ is rational with
non vanishing denominator there, hence continuous.

Mathlib does **not** package this continuity result. We prove it
inline by induction on the index $`i : \mathrm{Fin}\,n`$ using
`gramSchmidt_def`, which expresses

```math
\mathrm{gramSchmidt}(f)(i) = f(i) - \sum_{j \lt i} (\mathbb{R} \cdot \mathrm{gramSchmidt}(f)(j))\text{.starProjection}\,(f(i)).
```

Each term in the sum is continuous in $`f`$ by induction (the
projection onto a 1 dimensional subspace is the rational expression
$`(\langle v, w \rangle / \lVert v \rVert^2) \cdot v`$ via `Submodule.starProjection_singleton`,
which is continuous when $`\lVert v \rVert \ne 0`$, and the previous Gram, Schmidt
outputs are nonzero on the linearly independent locus).

This is the proof of `continuous_gramSchmidt_at`, which feeds into
`continuous_qMat_subtype`, `continuous_dMat_subtype`,
`continuous_uMat_subtype`, and finally `continuous_iwasawaSymm`.
Combining with the forward continuity gives `iwasawaHomeomorph`.
(This continuity result for `gramSchmidt` and `gramSchmidtNormed` is
itself a candidate Mathlib upstream contribution.)

### 4. Smooth structures on the easy three subgroups

The three "easy" subgroups admit single chart smooth structures.

**$`G n = GL_n(\mathbb{R})`$ as an open submanifold of $`\mathrm{Mat}_n(\mathbb{R})`$:** the
determinant map is continuous, so $`\{ g \in \mathrm{Mat}_n(\mathbb{R}) \mid \det g \ne 0 \}`$ is
open in $`\mathrm{Mat}_n(\mathbb{R})`$. Hence $`G n`$ is an open submanifold modeled on
$`\mathrm{Mat}_n(\mathbb{R})`$, with smooth structure provided by Mathlib's
`IsOpenEmbedding.singletonChartedSpace` and
`IsOpenEmbedding.isManifold_singleton`. The norm on $`\mathrm{Mat}_n(\mathbb{R})`$ is
chosen via `attribute [local instance]` as the standard sup of sup
norm `Matrix.normedAddCommGroup` (Mathlib intentionally does not
register a canonical matrix norm globally because several natural
choices exist). This is `instChartedSpaceG`, `instIsManifoldG`.

**$`UU\,n`$ as an affine slice of $`\mathrm{Mat}_n(\mathbb{R})`$:** an upper unipotent
matrix is $`1 + X`$ for $`X`$ strictly upper triangular (i.e.
$`X \in NN\,n = \mathfrak{n}`$), so the natural chart is the *translation*

```math
UU\,n \to NN\,n, \qquad U \mapsto U - 1
```

with inverse $`X \mapsto X + 1`$. Both maps are continuous (subtraction
and addition by a constant matrix), and the bijection is the
homeomorphism `UU.toNNHomeomorph`. The chart's source is all of
$`UU\,n`$, so we can use
`OpenPartialHomeomorph.singletonChartedSpace` to get
`ChartedSpace (NN n) (UU n)` and `IsManifold` modeled on the
normed space $`NN\,n`$ (a `Submodule` of $`\mathrm{Mat}_n(\mathbb{R})`$).

**$`A\,n`$ via diagonal logs:** a positive diagonal matrix is
characterized by its $`n`$ strictly positive diagonal entries; the
homeomorphism

```math
A\,n \to \mathbb{R}^n, \qquad D \mapsto (\log D_{11}, \ldots, \log D_{nn})
```

with inverse $`v \mapsto \mathrm{diag}(\exp v_1, \ldots, \exp v_n)`$ provides a single
chart. The map is well defined because $`D_{ii} \gt 0`$, so $`\log`$ is
continuous, and $`\exp v_i \gt 0`$ for all real $`v_i`$, so the inverse
lands back in $`A\,n`$. This is `A.toFinNRHomeomorph`. Modeled on
$`\mathrm{Fin}\,n \to \mathbb{R}`$ (Pi normed space).

### 5. The Cayley transform: parametrizing $`O(n)`$ by skew symmetric matrices

The hard subgroup is $`K = O(n)`$. Unlike $`G`$, $`A`$, $`UU`$, the
orthogonal group is not a single coordinate chart's worth of
material: it is a **compact closed submanifold** cut out by the
quadratic equations $`Q \cdot Q^T = 1`$. Single charts cannot cover
compact manifolds (the image would be both compact and
homeomorphic to an open subset of a Euclidean space, which is
impossible for compact manifolds of positive dimension).

The standard way around this is the **Cayley transform**, due to
Cayley (1846):

```math
\mathrm{cayley} : \mathrm{Mat}_n(\mathbb{R}) \to \mathrm{Mat}_n(\mathbb{R}), \qquad \mathrm{cayley}(X) = (1 - X)(1 + X)^{-1}.
```

Two crucial facts:

1. **$`(1 + X)`$ is invertible whenever $`X`$ is skew symmetric.** This
   is `one_add_skew_isUnit`. Proof: $`(1 + X)(1 - X) = 1 - X^2`$ and
   since $`X`$ is skew, $`X^2 = -X \cdot X^T`$, so $`1 - X^2 = 1 + X \cdot X^T`$. The
   matrix $`X \cdot X^T`$ is positive semi definite (it is the Gram matrix
   of the rows of $`X`$), so $`1 + X \cdot X^T`$ is positive definite, in
   particular invertible. Taking determinants of $`(1 + X)(1 - X) = 1 + X \cdot X^T`$
   shows $`\det(1 + X)^2 \gt 0`$, so $`\det(1 + X) \ne 0`$.

2. **$`\mathrm{cayley}(X)`$ is orthogonal whenever $`X`$ is skew symmetric.**
   This is `cayley_isOrthogonal`. Proof: a direct computation using
   that $`(1 - X)`$, $`(1 + X)`$ and their inverses all commute (because
   they are polynomials in $`X`$):

```math
\begin{aligned} \mathrm{cayley}(X) \cdot \mathrm{cayley}(X)^T &= (1 - X)(1 + X)^{-1} \cdot ((1 + X)^{-1})^T (1 - X)^T \\ &= (1 - X)(1 + X)^{-1} \cdot (1 + X^T)^{-1}(1 - X^T) \\ &= (1 - X)(1 + X)^{-1} \cdot (1 - X)^{-1}(1 + X) \\ &= (1 - X)(1 - X)^{-1} \cdot (1 + X)^{-1}(1 + X) \\ &= 1. \end{aligned}
```

In words: as $`X`$ ranges over skew symmetric matrices $`\mathrm{Sk}\,n`$, the
formula $`\mathrm{cayley}(X) = (1 - X)(1 + X)^{-1}`$ ranges over orthogonal
matrices $`Q`$ for which $`1 + Q`$ is invertible (i.e., $`-1`$ is not an
eigenvalue of $`Q`$). This is a dense open subset of $`O(n)`$, called
$`K_{\mathrm{open}}\,n`$ in our file.

The transform is **its own inverse**: applying $`\mathrm{cayley}`$ twice
returns the input (when both $`1 + X`$ and $`1 + \mathrm{cayley}(X)`$ are
invertible). This is `cayley_self_inverse`, proved by deriving
the algebraic identity

```math
1 - \mathrm{cayley}(X) = X \cdot (1 + \mathrm{cayley}(X))
```

(which holds for any $`X`$ with $`1 + X`$ invertible, and follows from
the two key Cayley identities $`(1 \pm \mathrm{cayley}(X))(1 + X)`$ proved as `one_add_cayley_mul` and
`one_sub_cayley_mul`), then dividing both sides by
$`1 + \mathrm{cayley}(X)`$ (also invertible).

Since `cayley` and `cayleyInv` have *the same formula*
$`(1 - M)(1 + M)^{-1}`$ (one is just the name we give to the function
when going one direction or the other), `cayley_self_inverse`
immediately gives both `cayleyInv ∘ cayley = id` on $`\mathrm{Sk}`$ and
`cayley ∘ cayleyInv = id` on $`K_{\mathrm{open}}`$. Bundling these gives
`cayleyEquiv`, the set theoretic bijection $`\mathrm{Sk}\,n \simeq K_{\mathrm{open}}\,n`$.

For the **continuity** of Cayley, both directions reduce to
continuity of matrix inversion on units, which Mathlib provides
via `continuousAt_matrix_inv` (matrix inverse is continuous at
any non singular matrix) plus `NormedRing.inverse_continuousAt`
(the abstract `Ring.inverse` is continuous at any unit). Bundling
gives `cayleyHomeomorph`, the topological bijection $`\mathrm{Sk}\,n \simeq_t K_{\mathrm{open}}\,n`$.

For the **smoothness** (i.e., $`C^\infty`$ ness), the same matrix inverse
on units lemmas give `ContDiff` smoothness of the underlying
matrix valued formulas; lifting to `ContMDiff` between manifolds
modeled on $`\mathrm{Sk}\,n`$ (with $`K_{\mathrm{open}}\,n`$ modeled via the Cayley chart
itself) is achieved through `contMDiff_isOpenEmbedding` and
`contMDiffOn_isOpenEmbedding_symm` plus a function equality
identification. Bundling all of this gives `cayleyDiffeomorph`, a
$`C^\infty`$ diffeomorphism between the
skew symmetric matrices and the dense open subset of $`O(n)`$.

### 6. The Sphere pattern multi chart atlas covering all of $`K = O(n)`$

Cayley centered at the identity covers $`K_{\mathrm{open}}\,n`$, the open subset
where $`1 + Q`$ is invertible. To cover the rest of $`O(n)`$ we follow
Mathlib's `Sphere.lean` pattern (Heather Macbeth, 2021): put a
Cayley chart **at every point** of $`K`$.

The translated Cayley chart at $`Q_0 \in K`$ is

```math
\mathrm{chart}_{Q_0} : K \to \mathrm{Sk}, \qquad \mathrm{chart}_{Q_0}(Q) = \mathrm{cayleyInv}(Q \cdot Q_0^T),
```

defined on the open subset $`K_{\mathrm{open\,at}}\,Q_0 = \{ Q \in K \mid 1 + Q \cdot Q_0^T \text{ invertible} \}`$. The inverse goes $`X \mapsto \mathrm{cayley}(X) \cdot Q_0`$. This is a
direct generalization of the identity centered chart and reduces to
it via the substitution $`Q' = Q \cdot Q_0^T`$ (which sends $`K_{\mathrm{open\,at}}\,Q_0`$
to $`K_{\mathrm{open}}`$ bijectively). The `cayleyEquivAt` in our file packages
this as $`\mathrm{Sk}\,n \simeq K_{\mathrm{open\,at}}\,Q_0`$.

The crucial covering property: **every $`Q \in K`$ lies in
$`K_{\mathrm{open\,at}}\,Q`$ itself**, because $`Q \cdot Q^T = 1`$ and $`1 + 1 = 2 \cdot 1`$
has determinant $`2^n \ne 0`$. This is `self_mem_K_open_at`. So the
family $`\{ K_{\mathrm{open\,at}}\,Q \mid Q \in K \}`$ is an open cover of $`K`$, and the
chart at $`Q`$ is `cayleyOpenChartAt Q`. Atlas: take all
`cayleyOpenChartAt Q₀` for $`Q_0`$ ranging over $`K`$.

This is `instChartedSpaceK`. The resulting `ChartedSpace (Sk n) (K n)`
gives $`K = O(n)`$ a topological manifold structure modeled on the
skew symmetric matrices. The `IsManifold` instance,
i.e., the smoothness of all chart transition maps, is `instIsManifoldK`,
which is now proved. The transition is

```math
\mathrm{chart}_{Q_1} \circ (\mathrm{chart}_{Q_0})^{-1} : X \in \mathrm{Sk} \mapsto \mathrm{cayleyInv}(\mathrm{cayley}(X) \cdot Q_0 \cdot Q_1^T),
```

defined on the open subset of $`\mathrm{Sk}\,n`$ where $`1 + \mathrm{cayley}(X) \cdot Q_0 \cdot Q_1^T`$
is invertible. This is a composition of three smooth pieces (cayley,
right multiplication by a fixed orthogonal matrix, cayleyInv), and
its smoothness reduces to standard `ContDiff` lemmas about matrix
multiplication and matrix inversion on units, plus
`isManifold_of_contDiffOn` to lift to `IsManifold`.

### 7. The Cartan Lie decomposition $`\mathfrak{gl}_n(\mathbb{R}) = \mathrm{Sym}_n \oplus \mathrm{Sk}_n`$

This is the simplest of the Lie algebra side decompositions and a
classical fact: every real square matrix is the sum of a symmetric
and a skew symmetric matrix in a unique way. The decomposition is

```math
M = \tfrac{1}{2}(M + M^T) + \tfrac{1}{2}(M - M^T),
```

with the symmetric part $`\tfrac{1}{2}(M + M^T) \in \mathrm{Sym}_n`$ and the
skew symmetric part $`\tfrac{1}{2}(M - M^T) \in \mathrm{Sk}_n`$. Uniqueness: if
$`M \in \mathrm{Sym} \cap \mathrm{Sk}`$ then $`M^T = M = -M`$, so $`2M = 0`$, so $`M = 0`$.

In Lean this is `cartanLieDecomp : IsCompl (Sym n) (Sk n)`, where
`IsCompl` is the lattice theoretic statement that $`\mathrm{Sym} \cap \mathrm{Sk} = \bot`$
(the disjoint condition) and $`\mathrm{Sym} \sqcup \mathrm{Sk} = \top`$ (the sum is everything
condition). `Sym` and `Sk` are realized as `Submodule ℝ Mat_n(ℝ)`.

This is exactly the Cartan decomposition in the sense of Lie theory: the
maximal compact subalgebra and its orthogonal complement under the trace form are

```math
\mathrm{Sk}_n = \mathrm{Lie}(O(n)) = \mathfrak{k}, \qquad \mathrm{Sym}_n = \mathfrak{p}.
```

The corresponding Cartan involution on the Lie algebra sends $`M`$ to $`-M^T`$,
with $`+1`$ eigenspace $`\mathfrak{k}`$ and $`-1`$ eigenspace $`\mathfrak{p}`$.

### 8. The Iwasawa Lie decomposition $`\mathfrak{gl}_n(\mathbb{R}) = \mathfrak{k} \oplus \mathfrak{a} \oplus \mathfrak{n}`$

This is the Lie algebra shadow of the Iwasawa group decomposition,
and the most substantial piece of pure linear algebra in the
project. The three subspaces are

```math
\mathfrak{k} = \mathrm{Sk}_n \quad (\text{skew symmetric matrices, } \mathrm{Lie}(O(n)))
```

```math
\mathfrak{a} = AA_n \quad (\text{real diagonal matrices, } \mathrm{Lie}(\text{positive diagonals}))
```

```math
\mathfrak{n} = NN_n \quad (\text{strictly upper triangular matrices, } \mathrm{Lie}(\text{upper unipotent}))
```

with dimensions $`n(n-1)/2 + n + n(n-1)/2 = n^2`$ summing to
$`\dim \mathfrak{gl}_n(\mathbb{R})`$.

We prove the four conditions for an internal direct sum
decomposition:

* `disjoint_AA_NN`: $`\mathfrak{a} \cap \mathfrak{n} = 0`$. A diagonal and strictly upper
  matrix has zero off diagonal entries (by $`\mathfrak{a}`$) and zero diagonal
  entries (by $`\mathfrak{n}`$), so it is the zero matrix.
* `disjoint_KK_AA`: $`\mathfrak{k} \cap \mathfrak{a} = 0`$. A skew diagonal matrix has
  $`M_{ii} = -M_{ii}`$ (skew), so $`M_{ii} = 0`$, and zero off diagonal
  by diagonality.
* `disjoint_KK_NN`: $`\mathfrak{k} \cap \mathfrak{n} = 0`$. Below the diagonal, strict upper
  membership gives $`M_{ij} = 0`$. On and above the diagonal we use
  skew symmetry: at $`(j, i)`$ for $`i \lt j`$ we have $`M_{ji} = 0`$ (below
  diagonal), and skew gives $`M_{ij} = -M_{ji} = 0`$.
* `iwasawa_codisjoint`: $`\mathfrak{k} + \mathfrak{a} + \mathfrak{n} = \mathfrak{gl}_n(\mathbb{R})`$. For any $`M`$, we
  construct the explicit decomposition

```math
A_{ij} = \begin{cases} M_{ii} & \text{if } i = j \\ 0 & \text{otherwise} \end{cases} \quad (\text{diagonal of } M)
```

```math
K_{ij} = \begin{cases} M_{ij} & \text{if } j \lt i \\ -M_{ji} & \text{if } i \lt j \\ 0 & \text{if } i = j \end{cases}
```

```math
N_{ij} = \begin{cases} M_{ij} + M_{ji} & \text{if } i \lt j \\ 0 & \text{otherwise} \end{cases}
```

  and verify $`A + K + N = M`$ on each of the three cases
  ($`j \lt i`$, $`j = i`$, $`i \lt j`$).

These four conditions, combined, give `iwasawaLieDecomp`, the full
internal direct sum statement.

### 9. The algebraic differential at the identity: $`\mathfrak{k} \times \mathfrak{a} \times \mathfrak{n} \simeq \mathfrak{gl}_n`$

The Lie algebra version of "the Iwasawa map is a diffeomorphism"
is "the Lie sum map is a linear isomorphism." We define

```math
\mathrm{iwasawaLieMap} : \mathfrak{k} \times \mathfrak{a} \times \mathfrak{n} \to_{\mathbb{R}} \mathfrak{gl}_n(\mathbb{R}), \qquad (X, Y, Z) \mapsto X + Y + Z
```

and prove:

* `iwasawaLieMap_surjective`: every $`M \in \mathfrak{gl}_n(\mathbb{R})`$ is in the image,
  immediately from `iwasawa_codisjoint`.
* `iwasawaLieMap_injective`: the kernel is trivial. Suppose
  $`X + Y + Z = 0`$ with $`X`$ skew, $`Y`$ diagonal, $`Z`$ strict upper.
  By the entry wise trichotomy:
    * $`j \lt i`$: $`Y_{ij} = 0`$ (off diagonal of a diagonal),
      $`Z_{ij} = 0`$ ($`j \le i`$ triggers strict upper zero), so
      $`X_{ij} = 0`$.
    * $`j = i`$: skew says $`X_{ii} = -X_{ii}`$, so $`X_{ii} = 0`$, and
      similarly the other two are zero on the diagonal.
    * $`i \lt j`$: by the previous case at $`(j, i)`$ we have $`X_{ji} = 0`$;
      skew gives $`X_{ij} = -X_{ji} = 0`$. The remaining $`Y_{ij}`$ and
      $`Z_{ij}`$ are zero by the same arguments as above.
  So $`X = Y = Z = 0`$.
* `iwasawaLieEquiv` bundles these as `LinearEquiv.ofBijective`.

This is the **algebraic differential at the identity** of the
Iwasawa map. The geometric statement `iwasawaMfderivAtIdentity`
identifies `mfderiv (iwasawaMap) (1, 1, 1)` with the corresponding
linear isomorphism, with the Cayley chart's first-order Taylor
expansion contributing a factor of $`-2`$ on the $`K`$-direction; it is
now proved.

This linear isomorphism is the "infinitesimal change of coordinates"
between the ambient Lie algebra $`\mathfrak{gl}_n(\mathbb{R})`$ and the Iwasawa Lie
factor $`\mathfrak{k} \times \mathfrak{a} \times \mathfrak{n}`$. It is the Lie algebra level Jacobian of the
Iwasawa map at the identity, and the inverse map $`M \mapsto (K, A, N)`$
gives the explicit formulas above.

## Milestones

All entries below except the final Haar row (milestone 7) are proved with
no `sorry`, and the diagnostic files print their axiom dependencies as
`[propext, Classical.choice, Quot.sound]`. Milestone 7, the Haar measure
pushforward, is the single exception: it is currently a quarantined
future-facing axiom in `IwasawaBridge.lean` (see
[Remaining Work](#remaining-work)).

| # | Goal | Status | Jorgenson and Lang reference |
|---|------|--------|---------------|
| 1   | `iwasawaEquiv : K × A × U ≃ GL_n(ℝ)` (set-theoretic bijection)                   | Proved   | Thm I.1.1, set-theoretic |
| 1b  | `inv_iwasawa_jl`: $`(kau)^{-1} = u^{-1} a^{-1} k^T`$ (Lang vs Jorgenson and Lang convention swap)            | Proved   | §I.1, p. 2              |
| 1b  | `cartanInvolution`, `cartanInvolution_involutive`                                | Proved   | §I.1, p. 2              |
| 2   | `continuous_iwasawaMap` (forward direction)                                      | Proved   | Thm I.1.1, topology     |
| 2   | `continuous_iwasawaSymm` (inverse direction; Gram-Schmidt continuity from scratch) | Proved | Thm I.1.1, topology     |
| 2   | `iwasawaHomeomorph : K × A × U ≃ₜ GL_n(ℝ)`                                       | Proved   | Thm I.1.1, topology     |
| 3   | `isOpen_G`, `G_isOpenEmbedding`, smooth structure on `G n`                       | Proved   | Thm I.1.1, smoothness   |
| 3   | `UU.toNNHomeomorph`, smooth structure on `UU n` (modeled on `NN n`)              | Proved   | Thm I.1.1, smoothness   |
| 3   | `A.toFinNRHomeomorph`, smooth structure on `A n` (modeled on `Fin n → ℝ`)        | Proved   | Thm I.1.1, smoothness   |
| 3   | Cayley transform setup (`cayley`, `cayleyInv`, `one_add_skew_isUnit`, `cayley_isOrthogonal`) | Proved   | Cayley 1846             |
| 3   | Cayley two-sided inverse (`cayley_self_inverse`, `cayleyInv_cayley`, `cayley_cayleyInv`) | Proved   | Cayley 1846             |
| 3   | `cayleyInv_isSkew` (image of orthogonal under Cayley is skew)                    | Proved   | Cayley 1846             |
| 3   | `cayleyEquiv : Sk n ≃ K_open n` (set-level Cayley bijection)                     | Proved   | Thm I.1.1, smoothness   |
| 3   | Cayley continuity (`continuous_cayley_on_skew`, `continuous_cayleyInv_on_KOpen`) | Proved   | Thm I.1.1, smoothness   |
| 3   | `cayleyHomeomorph : Sk n ≃ₜ K_open n` (topological)                              | Proved   | Thm I.1.1, smoothness   |
| 3   | Smooth manifold structure on `K_open n` modeled on `Sk n` via Cayley chart       | Proved   | Thm I.1.1, smoothness   |
| 3   | `cayleyDiffeomorph : Sk n ≃ₘ K_open n` ($`C^\infty`$ diffeomorphism)                     | Proved   | Thm I.1.1, smoothness   |
| 3   | `IsOrthogonal.mul`, `K_open_at`, `cayleyEquivAt Q₀ : Sk n ≃ K_open_at Q₀`        | Proved   | Thm I.1.1, multi-chart  |
| 3   | `self_mem_K_open_at` (cover $`\bigcup K_{\mathrm{open\,at}} Q = K\,n`$)                                | Proved   | Thm I.1.1, multi-chart  |
| 3   | `cayleyOpenChartAt Q₀ : OpenPartialHomeomorph (K n) (Sk n)` plus `instChartedSpaceK` | Proved   | Sphere-pattern atlas    |
| 3   | `instIsManifoldK` (chart transitions `ContDiffOn`, full `IsManifold` on $`K = O(n)`$) | Proved   | Thm I.1.1, full         |
| 3   | `iwasawaDiffeomorph : K × A × U ≃ₘ GL_n(ℝ)` (full diffeomorphism)                | Proved   | Thm I.1.1, full         |
| 4   | `cartanLieDecomp : IsCompl (Sym n) (Sk n)` (Cartan Lie decomp $`\mathfrak{gl}_n = \mathrm{Sym} \oplus \mathrm{Sk}`$) | Proved   | §I.3, p. 12             |
| 5   | `disjoint_AA_NN`, `disjoint_KK_AA`, `disjoint_KK_NN` (pairwise disjoint)         | Proved   | §I.3                    |
| 5   | `iwasawa_codisjoint`: $`\mathfrak{k} \sqcup \mathfrak{a} \sqcup \mathfrak{n} = \top`$ (sum is everything)                         | Proved   | §I.3                    |
| 5   | `iwasawaLieDecomp`: full Iwasawa Lie decomposition $`\mathfrak{gl}_n = \mathfrak{k} \oplus \mathfrak{a} \oplus \mathfrak{n}`$            | Proved   | §I.3                    |
| 5   | `iwasawaLieEquiv`: linear iso $`\mathfrak{k} \times \mathfrak{a} \times \mathfrak{n} \simeq_{\mathbb{R}} \mathfrak{gl}_n(\mathbb{R})`$ (algebraic differential at 1) | Proved | §I.3                    |
| 5   | `iwasawaMfderivAtIdentity` (geometric `mfderiv` at the identity)                 | Proved   | §I.3                    |
| 6   | `iwasawaMfderivAtFactored` (geometric `mfderiv` at a general $`(k, a, u)`$)        | Proved   | §I.2-I.3                |
| 6   | `det_sandwichOnSkCLM`: Sylvester-Franke $`\det(\Lambda^2 B) = (\det B)^{n-1}`$ on $`\mathrm{Sk}\,n`$ | Proved   | Jacobian density        |
| 6   | `adNN_det_eq_pair_product`: $`\det(\mathrm{ad}_{\mathfrak{n}}\, a) = \prod_{i \lt j} a_i / a_j`$ | Proved   | §I.2, Eq. (3)           |
| 6   | `detInIwasawaBases_fderiv_iwasawaCharted_general` (signed Jacobian determinant)  | Proved   | §I.2 Jacobian           |
| 6   | `absDetInIwasawaBases_fderiv_iwasawaCharted_general` (absolute Jacobian determinant) | Proved | §I.2 Jacobian           |
| 7   | Haar measure pushforward / change-of-variables identity                          | Quarantined axiom | §I.2, Prop. 2.1-2.4 |

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

/-- Milestone 5 and 6: geometric differential of the product map at the
identity and at a general point, in the project's charts. The `-2` on the
`K`-direction is the Cayley chart's first-order coefficient. -/
theorem iwasawaMfderivAtIdentity :
    ∀ (X : Sk n) (v : Fin n → ℝ) (Z : NN n),
      (mfderiv … (iwasawaMap : K n × A n × UU n → G n)
        (⟨1, _⟩, ⟨1, _⟩, ⟨1, _⟩)) (X, v, Z)
        = (-2 : ℝ) • X.1 + Matrix.diagonal v + Z.1
theorem iwasawaMfderivAtFactored (k : K n) (a : A n) (u : UU n) :
    mfderiv … (iwasawaMap : K n × A n × UU n → G n) (k, a, u)
      = iwasawaMatrixLeibnizCLM k a u

/-- Milestone 6: the Sylvester-Franke identity at k = 2. The congruence
`δ ↦ Bᵀ δ B` on the skew-symmetric matrices `Sk n ≃ Λ²(ℝⁿ)` has determinant
`(det B)^(n-1)`. -/
theorem det_sandwichOnSkCLM (B : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (sandwichOnSkCLM B).toLinearMap = B.det ^ (n - 1)

/-- Milestone 6: the closed-form Jacobian determinant of the charted Iwasawa
map at a general point `(X, v, Z)` of the chart domain, in the Iwasawa source
basis and the standard matrix target basis. Here `a = expDiagA v = diag(eᵛ)`,
`adNN a` is the conjugation action of `a` on the strictly-upper subalgebra, and
the final factor is the Cayley correction from the `K`-direction. -/
theorem detInIwasawaBases_fderiv_iwasawaCharted_general
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    detInIwasawaBases (fderiv ℝ (iwasawaCharted (n := n)) (X, v, Z)) =
      ((2 : ℝ) ^ Fintype.card (nnIndex n) *
          (expDiagA v).1.det ^ n * LinearMap.det (adNN (expDiagA v)).toLinearMap) *
        ((1 + X.1).det)⁻¹ ^ (n - 1)

theorem absDetInIwasawaBases_fderiv_iwasawaCharted_general
    (X : Sk n) (v : Fin n → ℝ) (Z : NN n) :
    absDetInIwasawaBases (fderiv ℝ (iwasawaCharted (n := n)) (X, v, Z)) =
      (2 : ℝ) ^ Fintype.card (nnIndex n) *
        |(expDiagA v).1.det| ^ n * |LinearMap.det (adNN (expDiagA v)).toLinearMap| *
        (|(1 + X.1).det|⁻¹) ^ (n - 1)

end IwasawaCoC
```

Here `Fintype.card (nnIndex n) = n(n-1)/2` is the number of strictly-upper
index pairs, so the leading factor is $`2^{\,n(n-1)/2}`$. At $`X = 0`$ the Cayley
correction $`((1 + 0).\det)^{-1\,(n-1)}`$ is $`1`$, and the formula reduces to the
chart-center value $`2^{\,n(n-1)/2}\,(\det a)^{n}\,\det\bigl(\mathrm{Ad}(a)|_{\mathfrak{n}}\bigr)`$;
this consistency is checked in `IwasawaComplete.lean`.

## Repository layout

```
iwasawa_change_of_coords/
├── README.md                    this file
├── IwasawaCoC.lean              core definitions, algebraic and topological layer
├── MatrixContDiff.lean          smoothness lemmas for matrix operations
├── IwasawaSmoothK.lean          full smooth manifold structure on K = O(n)
├── IwasawaDiffeomorph.lean      homeomorphism and full diffeomorphism
├── IwasawaLieDecomposition.lean Cartan and Iwasawa Lie decompositions
├── IwasawaMFDerivAtOne.lean     manifold differential at the identity
├── IwasawaMFDeriv.lean          manifold differential at a general point
├── IwasawaJacobianAbstract.lean abstract Jacobian / determinant scaffolding
├── IwasawaJacobianExplicit.lean explicit Jacobian: adNN determinant, transport CLMs
├── IwasawaComplete.lean         consolidated axiom-clean restatement,
│                                Sylvester-Franke identity, general-point Jacobian
├── IwasawaBridge.lean           quarantined future Haar / change-of-variables bridge
└── AxiomCheck*.lean             diagnostic files for axiom dependencies
```

The project shares the parent's Lake build (single `lakefile.toml`,
single `lean-toolchain`, single Mathlib pin), so there is no duplicated
toolchain configuration.

## Build instructions

From the workspace root (the directory containing `lakefile.toml`):

```sh
lake build
lake build iwasawa_change_of_coords.AxiomCheckDiffeomorph
lake build iwasawa_change_of_coords.AxiomCheckMFDerivAtOne
```

The first build will compile the parent project's `project.Iwasawa`
as a dependency.

## Verifying the result

After a successful build, the diagnostic files and the `#print axioms`
blocks at the end of `IwasawaComplete.lean` print axiom dependencies. The
consolidated file checks, among others,

```lean
IwasawaCoC.Complete.iwasawaDiffeo
IwasawaCoC.Complete.iwasawaMfderivAtIdentity
IwasawaCoC.Complete.iwasawaMfderivAtFactored
IwasawaCoC.Complete.det_sandwichOnSkCLM
IwasawaCoC.Complete.detInIwasawaBases_fderiv_iwasawaCharted_general
IwasawaCoC.Complete.absDetInIwasawaBases_fderiv_iwasawaCharted_general
```

each of which reports only `[propext, Classical.choice, Quot.sound]`. The
core namespace is `IwasawaCoC`, and the consolidated restatements live in
`IwasawaCoC.Complete`. `IwasawaComplete.lean` also contains compile-time
sanity checks: the scalar value $`\det(\mathrm{sandwich}(c \cdot 1)) = c^{\,n(n-1)}`$
at $`n = 3`$, the edge cases $`n = 0`$ and $`n = 1`$, and the consistency of the
general Jacobian at $`X = 0`$ with the chart-center value.

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

### Milestone 2: Topology and Gram, Schmidt continuity

`continuous_iwasawaMap` is one rule of `Continuous.matrix_mul` lifted
through subtype embeddings.

`continuous_iwasawaSymm` is the substantial piece. It reduces to
continuity of the parent project's Gram, Schmidt derived `qMat`, `dMat`,
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
  factors built from Gram, Schmidt outputs.
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

provides a parametrization of $`O(n)`$ minus a measure zero set by
skew symmetric matrices. The full chain:

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
  $`(1 \pm \mathrm{cayley}\,X)(1 + X) = X + X`$ and $`(1 + \mathrm{cayley}\,X)(1 + X) = 1 + 1`$.
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
dense subset of $`O(n)`$ where $`-1`$ is not an eigenvalue of $`Q`$). To
cover the rest of $`O(n)`$, we follow Mathlib's pattern from
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

## Remaining Work

The Jacobian-determinant layer is now complete: the determinant of the
charted Iwasawa map in the Iwasawa bases is proved in closed form at a
general point (`detInIwasawaBases_fderiv_iwasawaCharted_general` and its
absolute-value form), with the canonical derivative object
`iwasawaMatrixLeibnizCLM k a u`, the constant Cayley factor, the chart
conventions for `A` and `UU`, and the positive-root product
`adNN_det_eq_pair_product` all accounted for inside that formula.

The single remaining mathematical layer is the Haar measure pushforward:

1. Equip $`K`$, $`A`$, $`U`$, and $`G = GL_n(\mathbb{R})`$ with Haar measures and form the
   product measure on $`K \times A \times U`$.
2. Combine the pointwise absolute Jacobian determinant
   (`absDetInIwasawaBases_fderiv_iwasawaCharted_general`) with a Mathlib
   change-of-variables theorem to obtain the pushforward of the product
   Haar measure under the Iwasawa map.
3. Identify the resulting density with the Iwasawa character $`\delta(a)^{-1}`$
   and the global constant, recovering the integration formula below.
4. Replace the quarantined axiom in `IwasawaBridge.lean` with this
   measure-theoretic statement.

The target integration formula is

```math
\int_G f\,dx = c \int_U \int_A \int_K f(uak)\, \delta(a)^{-1}\, du\, da\, dk.
```

`IwasawaBridge.lean` is intentionally not part of the axiom-clean core yet.
It records the intended future Haar / change-of-variables endpoint and
currently contains one explicit axiom; every other result in the project is
reduced to `[propext, Classical.choice, Quot.sound]`.

## References

- J. Jorgenson, S. Lang. *Spherical Inversion on* $`SL_n(\mathbb{R})`$. Springer
  Monographs in Mathematics, 2001. (Primary source, Chapter I, §1 to §3.)
- S. Lang. *Linear Algebra*, 3rd edition. Springer Undergraduate Texts
  in Mathematics, 1987. (Convention for the parent project.)
- A. Cayley. "Sur quelques propriétés des déterminants gauches."
  *Crelle's Journal* 32 (1846), 119 to 123.
- The Mathlib community.
  [Mathlib4](https://github.com/leanprover-community/mathlib4).
- H. Macbeth. [`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html), 2021.
  (Stereographic projection multi chart atlas, the model we follow
  for `cayleyOpenChartAt`.)
- [`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html): transpose and inverse interaction.
- [`Mathlib.LinearAlgebra.Matrix.PosDef`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html): `PosDef.add_posSemidef`, `PosDef.isUnit`, `posSemidef_self_mul_conjTranspose` (used in `one_add_skew_isUnit`).
- [`Mathlib.Analysis.Matrix.Normed`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Normed.html): locally attributed matrix norm.
- [`Mathlib.Topology.Instances.Matrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/Matrix.html): continuity of matrix operations, including `continuousAt_matrix_inv` (used in `continuous_cayley_on_skew` and `continuous_cayleyInv_on_KOpen`).
- [`Mathlib.Geometry.Manifold.IsManifold.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold.Basic.html): `IsOpenEmbedding.isManifold_singleton`, `isManifold_of_contDiffOn`.
- [`Mathlib.Geometry.Manifold.Diffeomorph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Diffeomorph.html): `Diffeomorph` structure.

## License

Released for educational and academic use.

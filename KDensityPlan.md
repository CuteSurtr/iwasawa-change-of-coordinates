# KDensityPlan: discharging the SO(n) chart-domain nonemptiness blocker

Scope of this document: a single formalization blocker in `iwasawa_change_of_coords/IwasawaHaarK.lean`.
It records the precise statement, two candidate proof strategies with a Mathlib gap analysis
(researched against the pinned Mathlib, v4.30.0-rc1, under the mathlib package in `.lake/packages/mathlib`),
a short list of genuinely easy sub-lemmas that can be landed immediately, and an honest
recommendation. No `.lean` file is touched by this document; it is planning only.

## 1. The blocker, stated precisely

Definitions in play (file references are repo relative):

- `K n := { Q : Matrix (Fin n) (Fin n) ℝ // IsOrthogonal Q }` is the full orthogonal group O(n).
  Defined as `abbrev K` at `iwasawa_change_of_coords/IwasawaCoC.lean:64`.
- `cayley X = (1 - X)(1 + X)⁻¹`; `cayleyToK : Sk n → K n` is the Cayley chart
  (`iwasawa_change_of_coords/IwasawaCoC.lean:1014` and `:1108`).
- The matrix image of the Cayley map is
  `K_open n = { Q // IsOrthogonal Q and IsUnit (1 + Q).det }`
  (`abbrev K_open` at `iwasawa_change_of_coords/IwasawaCoC.lean:1283`), i.e. orthogonal matrices
  with no eigenvalue equal to -1. Throughout this document, C denotes this set of matrices
  (the Cayley image as a subset of O(n)).
- `det (cayley X) = 1` for every skew `X`. This is `det_cayley_skew` at
  `iwasawa_change_of_coords/IwasawaComplete.lean:1232` (note: it is declared `private`, and it
  lives in a different file from `IwasawaHaarK.lean`; see the note in Section 5). Consequently
  C is contained in SO(n).
- `cayleyLeftDom k0 = { X : Sk n | IsUnit (1 + k0 * cayley X).det }`
  (`def cayleyLeftDom` at `iwasawa_change_of_coords/IwasawaHaarK.lean:195`).

The blocker:

> For `k0` in SO(n) (that is, `det k0 = 1`), the set `cayleyLeftDom k0` is nonempty.

This is exactly the hypothesis `hne` of `cayleyLeftDom_compl_null`
(`iwasawa_change_of_coords/IwasawaHaarK.lean:480`), which is the measure-theoretic core
(the chart-miss set is the null zero locus of a nonzero polynomial). Without nonemptiness, the
polynomial could be identically zero and the conclusion would fail.

Reformulation. `1 + k0 * cayley X` is invertible exactly when `k0 * cayley X` lies in C
(the Cayley image, characterized by `1 + (.)` invertible). Since `cayley X` ranges over all of C
as `X` ranges over `Sk n`, nonemptiness of `cayleyLeftDom k0` is equivalent to:

> there exists `R` in C with `k0 * R` in C.

Two boundary facts that frame the problem honestly:

- For `k0` with `det k0 = -1` the set is genuinely empty: `k0 * cayley X` always has
  determinant -1, hence is not in SO(n), hence not in C (which sits inside SO(n)), so
  `1 + k0 * cayley X` is always singular. That component is handled by a separate reflected
  chart and is out of scope here. This is already noted in the source comment at
  `iwasawa_change_of_coords/IwasawaHaarK.lean:476`.
- The generic SO(n) case `X = 0` (when `1 + k0` is already invertible) is done and committed:
  `cayleyLeftDom_nonempty_of_one_add_unit` at `iwasawa_change_of_coords/IwasawaHaarK.lean:520`.
  The hard remaining case is `k0` in SO(n) with -1 in the spectrum of `k0`, the prototype being
  `k0 = -I` in even dimension (there `X = 0` fails because `1 + k0 = 0`).

## 2. Mathlib research findings

All searches were run read only against the pinned Mathlib under `.lake/packages/mathlib`.
File and line references are to that tree.

### 2.1 Connectedness of the relevant matrix groups

- `Matrix.orthogonalGroup` and `Matrix.specialOrthogonalGroup` are defined as abbreviations for
  `unitaryGroup` and `specialUnitaryGroup` at
  `Mathlib/LinearAlgebra/UnitaryGroup.lean:295` and `:315`.
- Connectedness or path connectedness of `Matrix.orthogonalGroup`, `Matrix.specialOrthogonalGroup`,
  any real SO(n), `specialLinearGroup`, or `generalLinearGroup`: ABSENT. No
  `IsConnected`, `IsPreconnected`, `ConnectedSpace`, `PreconnectedSpace`, `PathConnectedSpace`, or
  `IsPathConnected` instance or lemma was found for any of these matrix groups.
- The only connectedness result in the unitary direction is for the abstract unitary group of a
  unital complex C*-algebra: `Unitary.instLocPathConnectedSpace`
  (`Mathlib/Analysis/CStarAlgebra/Unitary/Connected.lean:377`). This is important to read
  carefully: (a) it is stated for `variable {A : Type*} [CStarAlgebra A]`
  (`Connected.lean:58`), a complex C*-algebra, not for the real matrix orthogonal group; and
  (b) it provides only LOCAL path connectedness (`LocPathConnectedSpace`), not a global
  `ConnectedSpace` or `PathConnectedSpace` instance. The file does prove that the path component
  of the identity is the set of products of exponential unitaries
  (`Unitary.mem_pathComponentOne_iff`, `Connected.lean:383`), but it never concludes that the
  whole unitary group is connected (it cannot, since that is false for general C*-algebras).
- Net: there is no off the shelf "SO(n) is connected" or "O(n) has two components" in this
  Mathlib pin. Any connectedness argument for the real special orthogonal group would have to be
  built from scratch.

### 2.2 Matrix exponential and surjectivity onto SO(n)

- `Matrix.exp` lives in `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`. Available:
  `Matrix.exp_transpose` (`:108`), `Matrix.exp_conjTranspose` (`:93`), and
  `Matrix.IsHermitian.exp` (`:97`).
- A general star-algebra fact `exp_mem_unitary_of_mem_skewAdjoint`
  (`Mathlib/Analysis/Normed/Algebra/Exponential.lean:539`) shows the exponential of a skew-adjoint
  element is unitary. In the real matrix instance, skew adjoint means `star A = -A`, i.e.
  `Aᵀ = -A`, so this specializes to "exp of a real skew matrix is orthogonal." That direction
  (skew exponentiates to orthogonal) is therefore essentially available, modulo wiring the
  `star = transpose` instance for `Matrix (Fin n) (Fin n) ℝ` and relating Mathlib `skewAdjoint`
  to the project `Sk n`.
- Surjectivity in the other direction (every element of SO(n) is `exp` of a skew matrix, the
  "exp : so(n) onto SO(n)" theorem): ABSENT. No "image is special orthogonal," "exp is surjective
  onto SO(n)," or equivalent was found. This is the substantive missing piece for any
  exp based route.

### 2.3 Real orthogonal / skew normal form (block rotation, Schur, spectral)

- Spectral theorem for Hermitian matrices: `Matrix.IsHermitian.spectral_theorem`
  (`Mathlib/Analysis/Matrix/Spectrum.lean:144`), stated over `RCLike` (so the complex or real
  Hermitian case with real eigenvalues, diagonalized by a unitary). There is also the linear-map
  spectral theorem in `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.
- Real block-diagonal 2x2 rotation normal form for orthogonal or skew-symmetric real matrices
  (the canonical form with 2x2 rotation blocks, used to prove `exp` surjects onto SO(n)):
  ABSENT. Searches for Schur form for general (non-Hermitian) matrices, block-diagonal rotation
  decomposition, and a canonical form for `skewAdjoint` real matrices returned nothing usable.
  The only "Schur" hits are the Schur product theorem (`Mathlib/Analysis/Matrix/Order.lean:247`)
  and categorical Schur's lemma, neither relevant.
- Rotation machinery that does exist is 2-dimensional and geometric:
  `Orientation.rotation` and `rightAngleRotation` in
  `Mathlib/Analysis/InnerProductSpace/TwoDim.lean`. There is no assembly of these into an
  n-dimensional block normal form.
- `Matrix.IsSkewAdjoint` and `skewAdjointMatricesSubmodule` exist
  (`Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean:562` and `:649`) but are about a
  sesquilinear-form notion of skew-adjointness, not directly the project's `Sk n`.

Conclusion for 2.2 and 2.3: the real normal form theory that would let one prove SO(n) = exp(so(n))
or directly factor SO(n) into Cayley-image pieces is not in this pin. Building it is a major
undertaking (real spectral or Schur theory for orthogonal matrices).

### 2.4 Topology lemmas for the dense-open-intersection route

These are present and directly usable:

- `Dense.inter_of_isOpen_left` and `Dense.inter_of_isOpen_right`
  (`Mathlib/Topology/Neighborhoods.lean:317` and `:322`): the intersection of a dense set with an
  open dense set is dense. This is the exact engine for "two dense opens have dense, hence
  nonempty, intersection."
- `dense_iff_inter_open` and its forward alias `Dense.inter_open_nonempty`
  (`Mathlib/Topology/Closure.lean:405` and `:415`): a dense set meets every nonempty open set.
- `Dense.nonempty` (`Mathlib/Topology/Closure.lean:427`): a dense set in a nonempty space is
  nonempty. Combined with the above, a dense intersection is nonempty once the ambient space is
  known nonempty.
- For a connectedness-flavored variant: `IsClopen.eq_univ`
  (`Mathlib/Topology/Connected/Clopen.lean:122`) and `IsPreconnected.union'`
  (`Mathlib/Topology/Connected/Basic.lean:125`) are available if one prefers a clopen argument,
  but they presuppose a `PreconnectedSpace` instance that does not exist for SO(n) (see 2.1).
- Baire space instances exist for completely metrizable spaces
  (`Mathlib/Topology/Baire/CompleteMetrizable.lean:26`) and for locally compact T2 spaces
  (`Mathlib/Topology/Baire/LocallyCompactRegular.lean:23`). These give "countable intersection of
  dense opens is dense" via `Mathlib/Topology/Baire/Lemmas.lean`. For just two dense opens, Baire
  is not needed; `Dense.inter_of_isOpen_left` already suffices, and it does not even require an
  ambient connectedness or Baire hypothesis.

## 3. Strategy (i): dense-open intersection inside SO(n)

Idea. Work inside the subspace SO(n). The Cayley image C is open in SO(n) (it is the locus where
`1 + (.)` is invertible, a preimage of an open set under a continuous determinant map; the same
argument already appears for `isOpen_cayleyLeftDom` at
`iwasawa_change_of_coords/IwasawaHaarK.lean:242`). If C is also dense in SO(n), then for fixed
`k0` in SO(n) the left translate `k0 . C` (the image of C under the homeomorphism "left multiply by
`k0`" of SO(n)) is again open and dense. Two dense opens have dense intersection
(`Dense.inter_of_isOpen_left`), which is nonempty since SO(n) is nonempty
(`Dense.nonempty`). A point of `C and k0 . C` gives `R` in C with `k0 . R = `(some element of C),
i.e. `k0⁻¹ . (element of C)` form, which is exactly the reformulated nonemptiness.

Mathlib pieces that exist:
- Openness of C in SO(n): the determinant-preimage argument is already in the repo for the
  analogous `cayleyLeftDom` set; re-deriving openness of C (or of `k0 . C`) is routine.
- Dense intersection of opens: `Dense.inter_of_isOpen_left` (Section 2.4). Solid, off the shelf.
- Nonempty from dense: `Dense.nonempty` (Section 2.4).
- Left multiplication by `k0` is a homeomorphism of SO(n) (continuous with continuous inverse,
  multiplication by a fixed orthogonal matrix), so it preserves "open" and "dense." Continuous
  matrix multiplication is available; packaging it as a `Homeomorph` of the subtype is light work.

The single real gap:
- DENSITY of C in SO(n): there is no Mathlib lemma. This is the crux. The standard math proof is
  that the complement is the set of orthogonal matrices having -1 as an eigenvalue, which is the
  zero locus inside SO(n) of `det (1 + Q)` (a nonzero real-analytic, indeed polynomial, function
  on the manifold SO(n)), hence has empty interior, hence C is dense. Formalizing "the zero set of
  a function that is not identically zero, restricted to a connected analytic manifold, is nowhere
  dense" needs either (a) connectedness of SO(n) plus a real-analytic identity-theorem style
  argument, or (b) a direct charted argument. Mathlib has the polynomial null-set tool the repo
  already uses (`MvPolynomial.volume_setOf_eval_eq_zero`, exploited in
  `cayleyLeftDom_compl_null`), but that gives measure-zero of the complement in the EUCLIDEAN
  chart `Sk n`, not topological density in the curved group SO(n). Bridging the Euclidean chart
  picture to a statement about all of SO(n) is precisely what is missing, and it is circular to
  use the chart for this, since the chart only covers C itself.

Honest assessment of strategy (i): the topology endgame (two dense opens meet) is trivial given
the inputs and uses only already-present lemmas (a few dozen lines). But the density input is NOT
in Mathlib and is genuinely hard. Proving density of C in SO(n) from scratch realistically requires
some of: connectedness of SO(n) (absent, 2.1), and either a real-analytic identity theorem on
manifolds or a hand built nowhere-dense argument for the eigenvalue -1 locus. Realistic effort:
the topology glue is small (about 40 to 80 lines), but the density lemma is a multi hundred line
project with significant prerequisite gaps (most of the work is reconstructing connectedness or a
manifold identity theorem). Difficulty: hard, dominated by a single missing theorem with no clean
Mathlib lever.

## 4. Strategy (ii): SO(n) = C . C (two Cayley factors)

Idea. It suffices to show every `g` in SO(n) factors as `g = R1 . R2` with `R1, R2` in C, because
then for a fixed target one rearranges to exhibit the required "`k0 . R` in C" witness. More
directly: C is symmetric under inverse (proved below in Section 5), and if SO(n) = C . C then for
any `k0` in SO(n) write `k0 = R1 . R2` with `R1, R2` in C; then `R2⁻¹` is in C and
`k0 . R2⁻¹ = R1` is in C, giving the witness `R := R2⁻¹` for the reformulated nonemptiness
("there is `R` in C with `k0 . R` in C"). So the whole blocker reduces to the covering statement
SO(n) = C . C.

Mathlib pieces that exist:
- C symmetric under inverse: provable now from `det_cayley_skew` plus standard determinant and
  inverse lemmas already used in the repo (`Matrix.transpose_nonsing_inv`,
  `Matrix.nonsing_inv_nonsing_inv`, multiplicativity of det). See Section 5.
- The reduction "C symmetric and SO(n) = C . C imply the blocker" is pure algebra, a few lines.

The single real gap:
- The covering SO(n) = C . C. There is no Mathlib lemma, and proving it is essentially as deep as
  proving exp surjects onto SO(n) or proving the real block-rotation normal form (2.2, 2.3, both
  ABSENT). Concretely, "every special orthogonal matrix is a product of two orthogonal matrices
  each lacking the eigenvalue -1" is a normal-form fact: in the 2x2 rotation block decomposition
  one writes each rotation as a product of two rotations none of which is the 180 degree rotation.
  But the block decomposition itself is not in Mathlib, so this route inherits the entire missing
  real spectral or Schur theory.

Honest assessment of strategy (ii): the reduction algebra and the symmetry lemma are easy and can
be landed today, but they only shift the blocker to SO(n) = C . C, which is at least as hard as the
density statement of strategy (i) and arguably harder, since it wants a constructive factorization
rather than a topological "generic" statement. Realistic effort: reduction and symmetry about 30 to
60 lines (easy); the covering theorem is a large project (real normal form, comparable to or
exceeding strategy (i)'s density lemma). Difficulty: hard, with a larger constructive burden.

## 5. Genuinely easy sub-lemmas that can be proven now

These do not resolve the blocker but are correct, self contained, and reduce or clarify it. They
can be added to `IwasawaHaarK.lean` (or a sibling) without any of the missing theory.

1. C is symmetric under inverse. For orthogonal `R` with `IsUnit (1 + R).det` (so `R` in C) and
   `det R = 1` (which holds because C is in SO(n) via `det_cayley_skew`), the inverse `R⁻¹ = Rᵀ`
   is again in C. Proof sketch: `det (1 + R⁻¹) = det (R⁻¹) . det (R + 1) = det (R + 1)` since
   `det R = 1` and `det (R⁻¹) = (det R)⁻¹ = 1`; the determinant lemmas and
   `Matrix.transpose_nonsing_inv` are already used in `IwasawaCoC.lean`
   (see `:184`, `:1086`, `:1119`). About 10 to 20 lines.

2. Restatement of the blocker as a coverage or translate-meets statement. Prove the equivalences,
   as standalone `iff` lemmas:
   - `(cayleyLeftDom k0).Nonempty` iff there exists `R` in C with `k0 . R` in C; and
   - given C symmetric, "there exists `R` in C with `k0 . R` in C" follows from "`k0` in C . C."
   These are pure rewriting on top of `mem_cayleyLeftDom_iff`
   (`iwasawa_change_of_coords/IwasawaHaarK.lean:338`) and the characterization of C by
   `1 + (.)` invertible. About 20 to 40 lines. This isolates the remaining mathematical content
   into one clean target (`k0` in C . C, or C dense in SO(n)).

3. Openness of C (and of `k0 . C`) as subsets of SO(n). The determinant-preimage argument is a copy
   of `isOpen_cayleyLeftDom` (`iwasawa_change_of_coords/IwasawaHaarK.lean:242`); packaging left
   multiplication by `k0` as a `Homeomorph` of the orthogonal-group subtype is routine continuity.
   About 30 to 50 lines. This makes strategy (i)'s topology endgame fully available, leaving only
   the density input.

4. The skew-exponentiates-to-orthogonal direction, as infrastructure. Wire the real-matrix
   `star = transpose` instance and apply `exp_mem_unitary_of_mem_skewAdjoint`
   (`Mathlib/Analysis/Normed/Algebra/Exponential.lean:539`) to conclude `Matrix.exp X` is
   orthogonal for `X` in `Sk n`. This does not give surjectivity (the hard direction) but is a
   reusable building block if an exp based attack is later attempted. About 20 to 40 lines.

Note on `det_cayley_skew`: it currently lives in `iwasawa_change_of_coords/IwasawaComplete.lean`
and is declared `private`. Sub-lemmas 1 and 2 need `det (cayley X) = 1` (equivalently `det R = 1`
for R in C) inside `IwasawaHaarK.lean`. The cheapest fix is a short non private restatement local to
`IwasawaHaarK.lean` (the proof is four or five lines: from `1 - X = (1 + X)ᵀ` one gets
`det (cayley X) . det (1 + X) = det (1 - X) = det (1 + X)`, then cancel the unit `det (1 + X)`),
rather than depending on the `private` lemma across files.

## 6. Recommendation (least risky path)

Recommended: pursue strategy (i) (dense-open intersection inside SO(n)), and in the immediate term
land the easy sub-lemmas of Section 5 (items 1 to 3 in particular).

Reasoning:

- The topological endgame of strategy (i) rests entirely on lemmas that are present and stable in
  this pin (`Dense.inter_of_isOpen_left`, `Dense.nonempty`, and the determinant-preimage openness
  pattern already in the repo). That part carries essentially no risk.
- Both strategies bottom out in one missing theorem (density of C in SO(n) for (i); SO(n) = C . C
  for (ii)). Between the two, the density statement of (i) is the milder target: it is a "generic
  position" statement (complement is a proper analytic subvariety, hence has empty interior),
  whereas (ii) demands an explicit constructive factorization that pulls in the full real
  block-rotation normal form. Generic, non constructive density is usually less code than a
  constructive normal form, and it composes with the already present topology lemmas.
- Strategy (ii)'s reduction is nonetheless cheap and worth landing as scaffolding (Section 5,
  items 1 and 2), because it provides a second independent attack surface and the symmetry lemma is
  reusable. But it should not be the primary route, since its core gap is the larger one.

Risk flag, stated plainly: even strategy (i) is not "just glue." Its density input is genuinely
absent from Mathlib and likely requires reconstructing connectedness of SO(n) or a real-analytic
identity theorem on manifolds, neither of which is present (Section 2.1, 2.3). The
realistic near term deliverable is therefore the Section 5 sub-lemmas plus the topology endgame of
(i) reduced to a single clearly stated `Dense C (in SO(n))` hypothesis, with that density lemma
itself scoped as a separate, larger effort. This keeps the committed code axiom clean and honest:
the remaining mathematical content is quarantined behind one named, well understood statement
rather than smuggled in.

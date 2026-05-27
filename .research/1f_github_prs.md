# Mathlib4 GitHub PRs (May 2025 to May 2026)

## Root systems and Cartan matrices

- **#39491** (OPEN, 2026-05-17, Suzuka Yu): Cartan matrix of a reduced crystallographic root system cannot have eigenvalue 4.
- **#38760** (MERGED, 2026-04-30, Oliver Nash): use Cartan's criterion for semisimplicity to drop redundant hypotheses.
- **#38749** (MERGED, 2026-04-30, jano-wol): Cartan's criterion for semisimplicity.
- **#37142** (MERGED, 2026-03-25, jano-wol): decompose ideal/Cartan intersection via coroot spans.
- **#34727** (MERGED, 2026-02-02, Oliver Nash): Geck construction yields a Lie algebra with the expected Cartan matrix.
- **#33557** (MERGED, 2026-01-04, Oliver Nash): a reduced crystallographic root system has a base.
- **#33321** (MERGED, 2025-12-26, Oliver Nash): linear independence of indecomposable roots of a root system.
- **#33013** (MERGED, 2025-12-17, Oliver Nash): roots linearly independent iff coroots are.
- **#32922** (MERGED, 2025-12-15, Oliver Nash): miscellaneous lemmas about root systems.
- **#32763** (MERGED, 2025-12-11, Jonathan Reich): Cartan matrices for classical types.
- **#29052** (MERGED, 2025-08-28, Oliver Nash): a root system is determined by its Cartan matrix.
- **#26965 / #26849 / #26819** (MERGED, July 2025, Oliver Nash): root system induction principles and Geck file reorganisation.
- **#25480** (MERGED, 2025-06-05, Oliver Nash): concrete model of the G2 root system.
- **#25285 / #25214** (MERGED, May 2025, Oliver Nash): Geck's construction of a Lie algebra from a root system.

## Killing form and semisimple Lie algebras

- **#36298** (MERGED, 2026-03-06, Oliver Nash): bases of semisimple Lie algebras and API.
- **#35326** (MERGED, 2026-02-14, jano-wol): root space decomposition of ideals of Lie algebras.
- **#34856** (MERGED, 2026-02-04, jano-wol): Killing orthogonal complement is complement.
- **#34584** (MERGED, 2026-01-29, stepan2698-cpu): definition of a semisimple representation.
- **#27237** (MERGED, 2025-07-17, Oliver Nash): Geck construction yields finite-dimensional semisimple Lie algebras.

## Lie algebra structure (loops, extensions, sl2)

- **#38594** (OPEN, 2026-04-28, Scott Carnahan): grading on loop algebras.
- **#37661 / #37520** (MERGED, April 2026, Pinyuan Chen): sl2 primitive vector and powers of `toEnd`.
- **#36653 / #36651** (MERGED, 2026-03-14, Leonid Ryvkin): LieDerivations under base change; compatible derivation pairs.
- **#36287** (MERGED, 2026-03-06, Scott Carnahan): graded Lie algebra class.
- **#35300** (MERGED, 2026-02-14, Leonid Ryvkin): semi-direct sum of Lie algebras.
- **#33690** (MERGED, 2026-01-06, Leonid Ryvkin): defining Lie-Rinehart algebras.
- **#33606** (MERGED, 2026-01-05, Scott Carnahan): basics of loop algebras.
- **#32896 / #31462 / #30891 / #29154** (MERGED, Aug 2025 to Dec 2025, Scott Carnahan): Lie algebra extensions, 2-cocycles, low-degree cochains.

## Lie groups, manifolds, Haar measure

- **#37932** (OPEN, 2026-04-11, idontgetoutmuch): **exponential map of a Lie group is smooth.** [PRIMARY INTEREST for T1-4 Lemma 1]
- **#33923** (MERGED, 2026-01-13, Michael Rothgang): fix example of GL(V) as a Lie group.
- **#38773** (MERGED, 2026-04-30, Yi Yuan): cleanup of `Haar/Quotient` rewrites.
- **#32672 / #32661** (MERGED, December 2025, Thomas Browning): Haar measures on short exact sequences.

## Author summary

Heather Macbeth and Eric Wieser do not appear as primary authors on this slice. Oliver Nash dominates root system and Killing form work, Scott Carnahan drives loop and extension theory, Leonid Ryvkin contributes Lie-Rinehart and derivation infrastructure. **No PRs on Iwasawa decomposition.** No PR on Cartan involution for real Lie groups (it's all over complex semisimple Lie algebras through Geck's construction). #37932 (exp smooth) is the only manifold-level Lie group PR in progress.

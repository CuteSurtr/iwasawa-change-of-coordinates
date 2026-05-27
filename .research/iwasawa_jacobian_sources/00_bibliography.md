# Bibliography: Iwasawa Jacobian and Haar Measure Sources

Collected 2026-05-25 for the `IwasawaCoC` Lean project (`iwasawa_change_of_coords`).
All listed sources are LEGAL: author-posted PDFs, arXiv, university lecture
notes, Wikipedia, or local mathlib. Books that are paywalled are listed
as "citation only".

## Tier A: Lie group, Iwasawa, Haar measure references

1. **Knapp, A. W.** *Lie Groups Beyond an Introduction, Digital Second
   Edition* (originally Birkhäuser, 2002; author's Digital 2nd ed. ~2023).
   Author-hosted full PDF:
   <https://www.math.stonybrook.edu/~aknapp/download/Beyond2.pdf>
   Frontmatter: <https://www.math.stonybrook.edu/~aknapp/books/green/beyond2-frontmatter.pdf>
   Relevance: Theorem 6.46 (Iwasawa for semisimple G); Examples 1 p. 371
   (SL(n, R), restricted roots); Proposition 8.43 (Haar decomposition
   `dx = e^{2ρ log a} dk da dn`); eq. 8.38 (`Δ = det Ad_n(a) = e^{2ρ log a}`).

2. **Helgason, S.** *Differential Geometry, Lie Groups, and Symmetric
   Spaces.* AMS GSM 34 (originally Academic Press 1978).
   Status: paywalled; citation only.
   Relevance: Chapter VI §3 to §5 (Iwasawa decomposition for noncompact
   semisimple Lie groups); Chapter I §5 (integration on Lie groups);
   SL(n, R)/SO(n, R) example; root multiplicity and ρ.

3. **Bump, D.** *Automorphic Forms and Representations.* CUP 1997.
   Status: partly viewable on Google Books; citation only for the book.
   Relevance: §2.3 (Iwasawa decomposition for GL(2, R)); general GL(n)
   extension in later chapters. Author site: <https://sporadic.stanford.edu/bump/>.

4. **Goldfeld, D., and Jacquet, H.** "Automorphic Representations and
   L-Functions for GL(n)." Goldfeld book chapter, author hosted.
   <https://www.math.columbia.edu/~goldfeld/LanglandsBookChapter.pdf>
   Relevance: Iwasawa decomposition `G(F) = A(F) N(F) K` with explicit
   GL(n, R) coordinates and Haar measure.

5. **Lei, A.** Notes on Goldfeld's GL(n, R) book, Columbia.
   <https://www.math.columbia.edu/~alei/autformsnotes/goldfeldnotes.pdf>
   Relevance: §1.4 gives `dμ(g) = ∏ dg_{ij} / det(g)^n` for the
   two-sided-invariant measure. §1.5 gives Iwasawa-coordinate Haar on
   the generalized upper half plane with explicit `y_k^{-k(n-k)-1}`
   factors.

6. **Conrad, K.** "Decomposing SL_2(R)." Expository note.
   <https://kconrad.math.uconn.edu/blurbs/grouptheory/SL(2,R).pdf>
   Relevance: Theorem 1.1 (SL_2(R) = KAN, unique factorization) and
   page 3 generalization to SL_n(R).

7. **Garrett, P.** Various GL(n) and Iwasawa expository notes, Minnesota.
   <http://www-users.cse.umn.edu/~garrett/m/v/>
   Relevance: detailed worked-out integration formulas on KAN; useful
   secondary source for cross-checking conventions.

8. **Dowd, C. J.** "Notes on Haar measures on Lie groups." UC Berkeley
   grad student notes (2023).
   <https://math.berkeley.edu/~cjdowd/haar1.pdf>
   Relevance: §3.1 derives the GL_n(R) Haar measure as `|det h|^{-n} dM`;
   §3.3 gives the GL_2(R) Iwasawa-coordinate Haar `du dx dy / (|u| y^2) dθ`.

9. **Schlicht, P.** "Iwasawa decomposition for GL(n, R)." Copenhagen Lie
   groups problem set.
   <https://web.math.ku.dk/~schlicht/Liegroups/IwasawaDecomp.pdf>
   Relevance: short, QR-style proof of `G = KB = KAN`.

10. **arXiv:1404.5535** (Hassi or related, 2014). "Abstract Harmonic
    Analysis on the General Linear Group."
    <https://arxiv.org/pdf/1404.5535>
    Relevance: eqs. (24) to (26) give the explicit Haar decomposition
    `∫_G f dg = ∫ f(kan) a^{2ρ} dn da dk` for SL_n(R).

11. **Jana, S.** "Cartan and Iwasawa Decompositions in Lie Theory."
    UBC notes.
    <https://personal.math.ubc.ca/~reichst/Cartan+Iwasawa.pdf>
    Relevance: SL_2(R) Iwasawa with `dx dy/y^2` Haar.

12. **Olafsson, G.** Chapter 6 "Basic Representation Theory."
    <https://www.math.lsu.edu/~olafsson/pdf_files/chaptr06.pdf>
    Relevance: Example 1 derives `μ = ∫ |det X|^{-n} dλ(X)` as left
    Haar on GL_n(R).

13. **Morel, S.** MAT 449 Problem Set 2 solutions, Princeton.
    <https://web.math.princeton.edu/~smorel/449/PS2_solutions.pdf>
    Relevance: explicit computation `det(c_a) = ∏ a_i^{n-2i+1}` and
    modular function `Δ_P(p) = ∏ a_i^{2i-n-1}` for the Borel.

14. **Wikipedia: "Iwasawa decomposition"**
    <https://en.wikipedia.org/wiki/Iwasawa_decomposition>
    Relevance: quick reference for `SL(n, R) = KAN` with `K = SO(n)`,
    `A = pos. diagonal det 1`, `N = upper unitriangular`.

15. **Wikipedia: "Haar measure"**
    <https://en.wikipedia.org/wiki/Haar_measure>
    Relevance: states `μ(S) = ∫_S |det X|^{-n} dX` for the GL_n(R)
    Haar measure.

## Tier B: QR / matrix-variate Jacobian references

16. **Mezzadri, F.** "How to generate random matrices from the classical
    compact groups," Notices of the AMS 54(5) (2007), 592 to 604.
    arXiv: <https://arxiv.org/abs/math-ph/0609050>
    PDF: <https://arxiv.org/pdf/math-ph/0609050>
    Published version: <https://www.ams.org/notices/200705/fea-mezzadri-web.pdf>
    Relevance: §5 covers QR with positive diagonal; gives the
    invariance argument identifying the Haar measure on U(N) via QR.

17. **Edelman, A., and Rao, N. R.** "Random matrix theory," Acta
    Numerica 14 (2005), 233 to 297. Author preprint at MIT.
    <https://math.mit.edu/~edelman/publications/random_matrix_theory.pdf>
    Relevance: eq. (3.6) gives the QR Jacobian for all three
    classical cases (β = 1, 2, 4) as `(dA) = ∏ r_ii^{β(m - i + 1) - 1} (dR) (Q^T dQ)`.
    For real square (β = 1, m = n): exponent on `r_ii` is `n - i`.

18. **Edelman, A.** MIT 18.338 handout 6, 18.325 handout 2.
    <http://www.mit.edu/~18.338/handouts/handout6.pdf>
    <https://web.mit.edu/18.325/www/handouts/handout2.pdf>
    Relevance: lecture-quality walk-through of the QR Jacobian and
    Stiefel manifold form `(Q^T dQ)`.

19. **Anderson, G. W., Guionnet, A., Zeitouni, O.** *An Introduction to
    Random Matrices.* CUP 2010. Author preprint at NYU.
    <https://cims.nyu.edu/~zeitouni/cupbook.pdf>
    Relevance: Appendix E, Corollary E.7 (existence and uniqueness of
    UT factorization with positive diagonal).

20. **Muirhead, R. J.** *Aspects of Multivariate Statistical Theory.*
    Wiley (1982, reprinted 2005).
    Status: paywalled; citation only.
    Relevance: Theorem 2.1.13 / 2.1.14 give the QR / Cholesky Jacobian
    in matrix-variate statistics notation. Authoritative reference.

21. **Diaz-Garcia, J. A., Gutierrez-Jaimez, R.** Several arXiv papers on
    QR / polar / SVD Jacobians. Search arXiv for the author pair.
    Relevance: matrix-variate statistics conventions; cross-checks.

22. **Wikipedia: "Wishart distribution"**
    <https://en.wikipedia.org/wiki/Wishart_distribution>
    Relevance: Bartlett decomposition `c_i^2 ~ χ^2_{n - i + 1}`,
    confirms the `r_ii^{n - i}` exponent independently via density
    matching with χ² distributions.

## Tier C: Local mathlib (read in place at .lake/packages/mathlib)

23. `Mathlib/LinearAlgebra/Determinant.lean` — `LinearMap.det`,
    `LinearMap.det_toMatrix`, `LinearMap.det_eq_zero_iff_ker_ne_bot`.

24. `Mathlib/LinearAlgebra/Matrix/StdBasis.lean` — `Matrix.stdBasis`,
    `Matrix.stdBasis_eq_single`.

25. `Mathlib/LinearAlgebra/Basis/Defs.lean` — `Basis.map`, `Basis.reindex`.

26. `Mathlib/LinearAlgebra/Basis/Prod.lean` — `Basis.prod`.

27. `Mathlib/LinearAlgebra/Matrix/Block.lean` — `Matrix.det_of_upperTriangular`,
    `Matrix.BlockTriangular`, block-determinant lemmas.

28. `Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean` — `Basis.addHaar`,
    `Basis.prod_addHaar`, `isAddHaarMeasure_basis_addHaar`.

29. `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean` — Haar
    utilities on finite-dim normed real spaces.

30. `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean` — `map_addHaar_smul`,
    `addHaar_smul`.

31. `Mathlib/MeasureTheory/Function/Jacobian.lean` — change-of-variables
    family: `lintegral_abs_det_fderiv_eq_addHaar_image`,
    `map_withDensity_abs_det_fderiv_eq_addHaar`,
    `integral_image_eq_integral_abs_det_fderiv_smul`,
    `restrict_map_withDensity_abs_det_fderiv_eq_addHaar`.

32. `Mathlib/MeasureTheory/Measure/Haar/Basic.lean` — abstract group
    Haar: `haarMeasure`, `isHaarMeasure_haarMeasure`,
    `isMulLeftInvariant_haarMeasure`.

33. `Mathlib/MeasureTheory/Measure/Haar/Unique.lean` — `haarMeasure_unique`,
    `haarScalarFactor`, `isMulLeftInvariant_eq_smul`.

34. `Mathlib/MeasureTheory/Group/ModularCharacter.lean` —
    `modularCharacter`, `modularCharacterFun`,
    `map_right_mul_eq_modularCharacterFun_smul`, `modularCharacterFun_pos`.

35. `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean` and
    `MulEquivHaarChar.lean` — distributional / mul-equiv Haar character
    machinery. `MathlibInfrastructureMap.md` §1c cites `distribHaarChar N (a) = |det Ad(a)|_𝔫|`.

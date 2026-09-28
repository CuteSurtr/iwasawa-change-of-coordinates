# Lean theorem statements

> Detailed reference for the [Iwasawa Decomposition and Change of Coordinates](../README.md) project. This page is long and dense with math, so GitHub may show it as source rather than rendering every formula. The short overview, with rendered status, is in the [README](../README.md).

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

/-- Milestone 5 (d), in `IwasawaLieDecomposition.lean`: `Sym_n = 𝔞 ⊕ 𝔫_sym`,
where `NNsym n = {X + Xᵀ : X ∈ NN n}`. -/
theorem sym_eq_aa_sup_nnSym : Sym n = AA n ⊔ NNsym n
theorem disjoint_AA_NNsym : Disjoint (AA n) (NNsym n)

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

/- Milestone 7: measure layer (namespace `IwasawaCoC.Complete`, `IwasawaHaar.lean`). -/

/-- `GL_n(ℝ)` is unimodular: its modular character is identically 1. -/
theorem modularCharacterFun_eq_one (g : G n) : Measure.modularCharacterFun g = 1

/-- The conjugation crux: `conjAut a` is `u ↦ a⁻¹ u a`, and pushing `haarN`
forward along it multiplies it by `δ(a) = det (adNN a) = ∏_{i<j} a_i/a_j`
(here as the `toNNReal` scalar). -/
lemma map_conjAut_haarN (a : A n) :
    Measure.map (conjAut a) (haarN (n := n))
      = (LinearMap.det (adNN a).toLinearMap).toNNReal • haarN

/-- Coordinate Haar equals canonical Haar up to a positive scalar (Haar uniqueness). -/
lemma nuG_eq_haarScalarFactor_smul_haarG :
    nuG (n := n) = Measure.haarScalarFactor (nuG (n := n)) haarG • haarG
lemma haarAExplicit_eq_haarScalarFactor_smul_haarA :
    haarAExplicit (n := n) = Measure.haarScalarFactor (haarAExplicit (n := n)) haarA • haarA
lemma nuU_eq_haarScalarFactor_smul_haarN :
    nuU (n := n) = Measure.haarScalarFactor (nuU (n := n)) haarN • haarN

/-- Integrals against `haarG` in matrix coordinates, with density `|det|^(-n)`
(`detWeightCoord`) over the invertible matrices (`Set.range gToCoord`). -/
theorem haarG_lintegral_eq_smul_setLIntegral_coord
    {F : ((Fin n × Fin n) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (Measure.haarScalarFactor (nuG (n := n)) haarG) • ∫⁻ x, F (gToCoord x) ∂(haarG (n := n))
      = ∫⁻ w in Set.range (gToCoord (n := n)), detWeightCoord w * F w ∂volume

/- Milestone 8: the integration formula (namespace `IwasawaCoC.Complete`,
`IwasawaIntegration.lean`). `iwasawaDeltaNN a = ∏_{i<j} a_i/a_j` as an `ℝ≥0`. -/

/-- `U` and `K = O(n)` are unimodular. -/
theorem modularCharacterFun_UU_eq_one (u : UU n) : Measure.modularCharacterFun u = 1
theorem modularCharacterFun_K_eq_one (k : K n) : Measure.modularCharacterFun k = 1

/-- The Iwasawa integration formula, Lang's order `g = k a u`. -/
theorem map_iwasawaMap_haar :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (iwasawaMap (n := n))
          ((haarK (n := n)).prod
            (((haarA (n := n)).withDensity fun a => (iwasawaDeltaNN a : ℝ≥0∞)).prod haarN))
        = c • haarG

/-- The same, as an integration formula. -/
theorem lintegral_iwasawa :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : G n → ℝ≥0∞, Measurable f →
      (c : ℝ≥0∞) * ∫⁻ g, f g ∂haarG
        = ∫⁻ k, ∫⁻ a, (iwasawaDeltaNN a : ℝ≥0∞) *
            ∫⁻ u, f (iwasawaMap (k, a, u)) ∂haarN ∂haarA ∂haarK

/-- Jorgenson and Lang's order `g = u a k`, with weight `δ(a)⁻¹`. -/
theorem map_iwasawaMapJL_haar :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (iwasawaMapJL (n := n))
          ((haarN (n := n)).prod
            (((haarA (n := n)).withDensity fun a => ((iwasawaDeltaNN a)⁻¹ : ℝ≥0)).prod
              haarK))
        = c • haarG

/-- The modular character of `B = A·U` (Mathlib's `Measure.modularCharacterFun`) at
`a ∈ A` is `δ(a)`. Here `toBB (a, 1)` is `a` as an element of `B`. -/
theorem modularCharacterFun_toBB (a : A n) :
    Measure.modularCharacterFun (toBB (a, 1)) = iwasawaDeltaNN a

/- The explicit Haar measure on K in Cayley coordinates (namespace
`IwasawaCoC.Complete`, `IwasawaHaarK.lean`); not needed for the integration formula.
The exponent −(n−1) is read off `det_sandwichOnSkCLM`. -/

/-- The intrinsic Cayley chart derivative on `Sk n`, equal to `-2 • sandwichOnSkCLM ((1+X)⁻¹)`. -/
noncomputable def cayleyDerivOnSk (X : Sk n) : Sk n →L[ℝ] Sk n
theorem det_cayleyDerivOnSk (X : Sk n) :
    LinearMap.det (cayleyDerivOnSk X).toLinearMap
      = (-2 : ℝ) ^ Fintype.card (nnIndex n) * ((1 + X.1).det)⁻¹ ^ (n - 1)

/-- The corrected left invariant Cayley density and the candidate invariant measure. -/
noncomputable def rhoK (X : Sk n) : ℝ≥0∞ := ENNReal.ofReal ((|(1 + X.1).det|⁻¹) ^ (n - 1))
noncomputable def nuK : Measure (K n) := Measure.map cayleyToK (volSk.withDensity rhoK)

/-- The Mobius left translation and the geometric heart of left invariance. -/
noncomputable def cayleyLeftTrans (k₀ : K n) (X : Sk n) : Matrix (Fin n) (Fin n) ℝ
theorem cayley_cayleyLeftTrans (k₀ : K n) {X : Sk n} (hX : X ∈ cayleyLeftDom k₀) :
    cayley (cayleyLeftTrans k₀ X) = k₀.1 * cayley X.1
theorem mem_cayleyLeftDom_iff (k₀ : K n) (X : Sk n) :
    X ∈ cayleyLeftDom k₀ ↔ ((1 + X.1) + k₀.1 * (1 - X.1)).det ≠ 0

/-- The domain of the Mobius translation is co-null once it is nonempty, and it is
nonempty when `1 + k₀` is invertible. -/
theorem cayleyLeftDom_compl_null (k₀ : K n) (hne : (cayleyLeftDom k₀).Nonempty) :
    volSk (cayleyLeftDom k₀)ᶜ = 0
lemma cayleyLeftDom_nonempty_of_one_add_unit (k₀ : K n) (h : IsUnit (1 + k₀.1).det) :
    (cayleyLeftDom k₀).Nonempty

/-- Haar uniqueness reduces `nuK = c • haarK` to left invariance and regularity. -/
theorem nuK_eq_smul_haarK_of_invariant
    [IsFiniteMeasureOnCompacts (nuK (n := n))] [Measure.IsMulLeftInvariant (nuK (n := n))]
    [Measure.InnerRegular (nuK (n := n))] :
    (nuK (n := n)) = Measure.haarScalarFactor (nuK (n := n)) (haarK (n := n)) • (haarK (n := n))

end IwasawaCoC

/-- Reusable measure theory lemma (`PolynomialNullSet.lean`, namespace `MvPolynomial`):
the zero set of a nonzero real polynomial in finitely many variables is Lebesgue null. -/
theorem MvPolynomial.volume_setOf_eval_eq_zero
    {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (hp : p ≠ 0) :
    volume {x : Fin d → ℝ | eval x p = 0} = 0
```

Here `Fintype.card (nnIndex n) = n(n-1)/2` is the number of strictly-upper
index pairs, so the leading factor is $`2^{\,n(n-1)/2}`$. At $`X = 0`$ the Cayley
correction $`((1 + 0).\det)^{-1\,(n-1)}`$ is $`1`$, and the formula reduces to the
chart-center value $`2^{\,n(n-1)/2}\,(\det a)^{n}\,\det\bigl(\mathrm{Ad}(a)|_{\mathfrak{n}}\bigr)`$;
this consistency is checked in `IwasawaComplete.lean`.

## Milestone index

Where each piece sits relative to Jorgenson and Lang, *Spherical Inversion on*
$`SL_n(\mathbb{R})`$, Chapter I. Everything listed is proved except the last row.

| # | Result | Jorgenson and Lang |
|---|--------|--------------------|
| 1 | `iwasawaEquiv : K × A × U ≃ GL_n(ℝ)` | Thm I.1.1, set theoretic part |
| 1b | `inv_iwasawa_jl`: $`(kau)^{-1} = u^{-1} a^{-1} k^T`$, Lang's order to theirs | §I.1, p. 2 |
| 1b | `cartanInvolution`, `cartanInvolution_involutive` | §I.1, p. 2 |
| 2 | `continuous_iwasawaMap`, `continuous_iwasawaSymm`, `iwasawaHomeomorph` | Thm I.1.1 |
| 3 | smooth structures on `G n`, `UU n`, `A n`; the Cayley transform (`cayley`, `cayleyInv`, `cayleyEquiv`, `cayleyHomeomorph`, `cayleyDiffeomorph`) | Thm I.1.1; Cayley 1846 |
| 3 | the atlas `cayleyOpenChartAt`, `instChartedSpaceK`, `instIsManifoldK` | Thm I.1.1 |
| 3 | `iwasawaDiffeomorph : K × A × U ≃ₘ GL_n(ℝ)` | Thm I.1.1 |
| 4 | `cartanLieDecomp`: $`\mathfrak{gl}_n = \mathrm{Sym} \oplus \mathrm{Sk}`$ | §I.3, p. 12 |
| 5 | `iwasawaLieDecomp`, `iwasawaLieEquiv`: $`\mathfrak{gl}_n = \mathfrak{k} \oplus \mathfrak{a} \oplus \mathfrak{n}`$ | §I.3 |
| 5 | `sym_eq_aa_sup_nnSym`, `disjoint_AA_NNsym`: $`\mathrm{Sym} = \mathfrak{a} \oplus \mathfrak{n}_{\mathrm{sym}}`$ | §I.3, p. 14 |
| 5 | `iwasawaMfderivAtIdentity`: the differential at the identity | §I.3 |
| 6 | `iwasawaMfderivAtFactored`: the differential at a general point | §I.2, §I.3 |
| 6 | `det_sandwichOnSkCLM`: Sylvester-Franke, $`(\det B)^{n-1}`$ on $`\mathrm{Sk}_n`$ | |
| 6 | `adNN_det_eq_pair_product`: $`\det(\mathrm{Ad}(a)\vert_{\mathfrak{n}}) = \prod_{i<j} a_i / a_j`$ | §I.2, Eq. (3) |
| 6 | `absDetInIwasawaBases_fderiv_iwasawaCharted_general`: the Jacobian determinant | §I.2 |
| 7 | `modularCharacterFun_eq_one`: $`GL_n(\mathbb{R})`$ is unimodular | §I.2 |
| 7 | `map_conjAut_haarN`: pushing $`\mathrm{haar}_N`$ along $`u \mapsto a^{-1}ua`$ multiplies it by $`\delta(a)`$ | §I.2, Eq. (1) to (3) |
| 7 | `nuG_eq_haarScalarFactor_smul_haarG`, `haarAExplicit_eq_…`, `nuU_eq_…`: explicit Haar measures | §I.2 |
| 7 | `haarG_lintegral_eq_smul_setLIntegral_coord`: integrals against $`\mathrm{haar}_G`$ in matrix coordinates | |
| 7 | `det_cayleyDerivOnSk`, `nuK`, `cayleyLeftTrans`, `mem_cayleyLeftDom_iff`, `cayleyLeftDom_compl_null`, `nuK_eq_smul_haarK_of_invariant`: Haar measure on $`K`$ in Cayley coordinates (partial) | |
| 7 | `MvPolynomial.volume_setOf_eval_eq_zero`: polynomial zero sets are null | |
| 8 | `map_iwasawaMap_haar`, `lintegral_iwasawa`, `map_iwasawaMapJL_haar`: the integration formula | §I.2, Prop. 2.1 to 2.4 |
| 8 | `modularCharacterFun_toBB`: the modular character of $`B = AU`$ on $`A`$ is $`\delta`$ | §I.2 |
| | not done: left invariance, finiteness on compacts and inner regularity of `nuK` (which together give `nuK = c • haarK`), nonemptiness of `cayleyLeftDom k₀` for $`k_0 \in SO(n)`$ with eigenvalue $`-1`$, the $`\det = -1`$ component | |

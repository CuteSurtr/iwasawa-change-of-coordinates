# L3-B/C/D/F: Mathlib4 patterns + worked analogue

## B. Product manifold chart structure

**`ChartedSpace` product instance** — `Mathlib/Geometry/Manifold/ChartedSpace.lean:435-441`:
```lean
instance prodChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (H' : Type*) [TopologicalSpace H'] (M' : Type*) [TopologicalSpace M']
    [ChartedSpace H' M'] : ChartedSpace (ModelProd H H') (M × M') where
  atlas := image2 OpenPartialHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
```
Note: model space is `ModelProd H H'` (type synonym for `H × H'`) to avoid defeq diamonds.

**`OpenPartialHomeomorph.prod`** — `Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean:81-87`:
```lean
def prod (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    OpenPartialHomeomorph (X × Y) (X' × Y')
```

**`ModelWithCorners.prod`** — `Mathlib/Geometry/Manifold/IsManifold/Basic.lean:500-523`:
```lean
def ModelWithCorners.prod (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H')
```

**`chartAt` product decomposition** — `prodChartedSpace_chartAt` at `ChartedSpace.lean:452-455` (`@[simp, mfld_simps]`):
```lean
theorem prodChartedSpace_chartAt :
    chartAt (ModelProd H H') x = (chartAt H x.fst).prod (chartAt H' x.snd) := rfl
```

**`extChartAt` product decomposition** — `extChartAt_prod` at `IsManifold/ExtChartAt.lean:864-867`:
```lean
theorem extChartAt_prod (x : M × M') :
    extChartAt (I.prod I') x = (extChartAt I x.1).prod (extChartAt I' x.2)
```
**NOT** tagged `@[simp, mfld_simps]` — must `rw [extChartAt_prod]` explicitly.

Also: `writtenInExtChartAt_prod` at `IsManifold/ExtChartAt.lean:835-839` for `Prod.map f g`.

## C. `writtenInExtChartAt` unfolding

**Definition** — `Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:800-802`:
```lean
@[simp, mfld_simps]
def writtenInExtChartAt (x : M) (f : M → M') : E → E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm
```
Definition itself is `@[simp, mfld_simps]`, so `simp only [writtenInExtChartAt]` or `simp only [mfld_simps]` unfolds. No separately-named `writtenInExtChartAt_def`.

**Model-space simp shortcut** — `writtenInExtChartAt_model_space` at `MFDeriv/FDeriv.lean:50-51`:
```lean
@[mfld_simps]
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f := rfl
```

**Singleton-chart open submanifold (our `G n`).** Mathlib does NOT provide a dedicated rewriter. The pattern: `chartAt _ x = Subtype.val` definitionally for `IsOpenEmbedding.singletonChartedSpace`, so `writtenInExtChartAt` unfolds to `Subtype.val ∘ f ∘ Subtype.val.symm`. The `singletonChartedSpace_chartAt_eq` lemma at `Mathlib/Geometry/Manifold/HasGroupoid.lean:211-214` is `@[simp, mfld_simps]` and makes this work. See `Units Rˣ` workflow in `Mathlib/Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean` (line 41-45) for the template: `chartAt_apply : chartAt R a b = b` and `chartAt_source : (chartAt R a).source = univ` as `rfl`.

## D. `HasFDerivAt → HasMFDerivAt` bridge

**Model-space-only direct bridge** — `Mathlib/Geometry/Manifold/MFDeriv/FDeriv.lean:61-65`:
```lean
theorem hasMFDerivAt_iff_hasFDerivAt {f'} :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ HasFDerivAt f f' x

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt
```
**Vector-space source AND target only.** NOT directly applicable to general manifolds.

**General-manifold idiom.** Unfold `HasMFDerivAt` via its definition (`MFDeriv/Defs.lean:313-315`):
```lean
def HasMFDerivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)
```
To promote a `HasFDerivAt` of the chart-pulled-back representative to a `HasMFDerivAt`: supply the pair `⟨hf_continuous, hf_fderiv.hasFDerivWithinAt⟩` (use `HasFDerivAt.hasFDerivWithinAt` to weaken to `range I`). Companion within-set form: `hasMFDerivWithinAt_iff_hasFDerivWithinAt` (alias `HasFDerivWithinAt.hasMFDerivWithinAt`) at `MFDeriv/FDeriv.lean:53-59`.

In practice, also use `HasFDerivWithinAt.congr_of_eventuallyEq` so the actual representative matches the hand-derived `f'` near `(extChartAt I x) x`.

## F. Worked analogue: `hasMFDerivAt_sumSwap`

Location: `Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:664-670`.

```lean
theorem hasMFDerivAt_sumSwap :
    HasMFDerivAt% (@Sum.swap M M') p (ContinuousLinearMap.id 𝕜 (TangentSpace I p)) := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp
```

**Function**: `Sum.swap : M ⊕ M' → M' ⊕ M`, computed at fully general `p : M ⊕ M'`.
**Formula**: mfderiv at `p` = identity (modulo TangentSpace defeq).

**Technique outline** (THE template to follow for `mfderiv_iwasawaMap_at_factored`):

1. **Use `HasMFDerivAt` definitional pair.** `refine ⟨_, _⟩` splits into:
   (a) continuity (`by fun_prop`)
   (b) `HasFDerivWithinAt (writtenInExtChartAt ...)` at `(extChartAt I p) p` over `range I`.

2. **Show chart representative locally equals a hand-built function** via a separate eventually-eq lemma (`writtenInExtChartAt_sumSwap_eventuallyEq_id` at lines 634-662). It cases on `p`, takes open set `t = I.symm ⁻¹' (chartAt H x).target ∩ range I`, and proves pointwise equality via:
   - `simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl, ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]`
   - Then `Sum.inr_injective.extend_apply`, `(chartAt H x).right_inv`, `I.right_inv`.
   - Neighborhood membership: `I.continuousWithinAt_symm.preimage_mem_nhdsWithin` + `self_mem_nhdsWithin`.

3. **Transport derivative via `HasFDerivWithinAt.congr_of_eventuallyEq`**:
   - Start: `hasFDerivWithinAt_id _ (range I) : HasFDerivWithinAt id (.id _) (range I) _`.
   - Apply with the eventually-eq proof + basepoint equality (`simp only [mfld_simps]` + `cases p <;> simp`).

4. **NO `HasMFDerivAt.comp` and NO `HasFDerivAt.hasMFDerivAt`** because source/target are not vector-space models. Custom route: build the `HasMFDerivAt` pair directly using `writtenInExtChartAt` unfolding + `HasFDerivWithinAt.congr_of_eventuallyEq`.

**This is precisely the template for our `mfderiv_iwasawaMap_at_factored`**: prove `writtenInExtChartAt I_prod I_M (k, a, u) iwasawaMap` locally equals an explicit `f : Sk × (Fin n → ℝ) × NN → Matrix _ _ ℝ` (via product chart unfolding + `Subtype.val` singleton chart), then use `HasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq` to transport the matrix-Leibniz CLM derivative onto the `HasMFDerivAt` goal.

### Key file paths

- `Mathlib/Geometry/Manifold/ChartedSpace.lean`
- `Mathlib/Geometry/Manifold/IsManifold/Basic.lean`
- `Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean`
- `Mathlib/Geometry/Manifold/HasGroupoid.lean`
- `Mathlib/Geometry/Manifold/MFDeriv/Defs.lean`
- `Mathlib/Geometry/Manifold/MFDeriv/FDeriv.lean`
- `Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean` (lines 128, 664)
- `Mathlib/Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean`
- `Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean`

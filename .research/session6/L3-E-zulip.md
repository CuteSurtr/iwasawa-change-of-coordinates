# L3-E: Lean Zulip threads on manifold derivative elaboration (4 threads)

## 1. Grassmannians (#mathlib4)
- URL: https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Grassmannians.html
- Date: Oct 10-11, 2023
- Summary: Sophie Morel's Grassmannian formalization hit the ChartedSpace model-space ambiguity. Two options debated: make the model space ε an explicit argument to Grassmannian, or choose ε canonically via choice.
- Advice (Sébastien Gouëzel): the model space in ChartedSpace is deliberately explicit "to allow for different charted space structures on the same type." Library was deliberately switched away from outParam for the model "to avoid nasty diamonds with products." Concrete takeaway: pass I and the model space explicitly at the call site; do not expect typeclass inference to recover them.

## 2. Projective space (#mathlib4)
- URL: https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Projective.20space.html
- Date: 2023
- Summary: Morel's smooth-manifold structure on projective space. Discussion of chart indexing and model space choice, with Massot and Gouëzel weighing integration strategy.
- Advice: reinforces the explicit-I pattern; consensus that chart definitions should be parameterized by an explicit H rather than left implicit.

## 3. Smooth varieties are smooth manifolds (#new-members)
- URL: https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Smooth.20varieties.20are.20smooth.20manifolds.html
- Date: Dec 7, 2021 onward
- Summary: Strategy thread on preimage-of-regular-value and submanifold construction.
- Advice (Heather Macbeth): warm up with smaller targets (projective space, Grassmannians) before tackling general regular-value preimages. (Patrick Massot): the regular-value preimage theorem is the load-bearing lemma to target. (Gouëzel): preimage theorems fail for manifolds-with-corners; pathological example x → e^(−1/x²) sin(1/x). Tactical takeaway: pick ModelWithCorners.Boundaryless instances when you want clean preimage results.

## 4. New attribute to mark theorems (#lean4)
- URL: https://leanprover-community.github.io/archive/stream/270676-lean4/topic/New.20attribute.20to.20mark.20theorems.html
- Date: Oct 2, 2021
- Summary: Discussion of porting custom simp attributes to Lean 4. Johan Commelin cites mfld_simps as the canonical example (originally declared in data/equiv/local_equiv.lean). Leonardo de Moura recommends Lean.Meta.Tactic.Simp.SimpLemmas API over the old mk_simp_attribute command.
- Advice: when stuck unfolding chart-level goals, use simp only [...] with mfld_simps (or simp only [mfld_simps] in Lean 4) rather than bare simp — the curated set is what closes extChartAt/writtenInExtChartAt goals without blowup.

## Cross-cutting tactical guidance (synthesized)

- mfderiv I I' f x unfolds to ordinary fderiv of writtenInExtChartAt I I' x f at (extChartAt I x) x. When mfderiv lemmas refuse to apply, transfer via mfderiv_eq_fderiv or MDifferentiableAt.hasMFDerivAt, then close the linear-map goal.
- For products: never let ModelWithCorners be inferred. Write I.prod I' explicitly; identity-on-E×F vs product model are NOT defeq.
- Composition: prefer HasMFDerivAt.comp over mfderiv_comp (bundled version threads MDifferentiableAt hypotheses cleanly).
- For mfld_simps: use as simp only [..., mfld_simps] to unfold extChartAt, chartAt, PartialHomeomorph.extend simultaneously.

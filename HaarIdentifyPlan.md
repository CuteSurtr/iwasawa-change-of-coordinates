# haarG identification plan (branch `haar-identify`)

Goal: identify `haarGCoord` with `haarG` on `G n` and conclude
`Measure.modularCharacterFun (g : G n) = 1` (unimodularity of GL_n(R)).

## Ground truth (verified this session)
- `G n = { g : Matrix (Fin n) (Fin n) R // g.det != 0 }` (IwasawaCoC.lean:74, `abbrev`, `n` explicit).
- `haarG : Measure (G n) := Measure.haar` with `IsHaarMeasure` (IwasawaComplete.lean:1910).
- `G_coe_mul : ((g*h : G n) : Matrix) = g.1 * h.1` (rfl) (IwasawaComplete.lean:1661).
- `matrixToCoord : Matrix =L (Fin n x Fin n -> R)` (LinearEquiv) (IwasawaHaar.lean:795).
- `leftMulCoord/rightMulCoord g = matrixToCoord.conj (left/rightMulMatLin g)`.
- `haarGCoord = volume.withDensity detWeightCoord` (IwasawaHaar.lean:925), bi invariant:
  `map_leftMulCoord_haarGCoord`, `map_rightMulCoord_haarGCoord`.
- `detWeightCoord w = ofReal ((|(matrixToCoord.symm w).det| ^ n)^{-1})`; finite valued; `0` on det=0.

## Mathlib API confirmed available
- `MeasurableEmbedding.comap_apply (mu) (s) : comap f mu s = mu (f '' s)` (Restrict.lean:891)
- `MeasurableEmbedding.map_comap (mu) : (comap f mu).map f = mu.restrict (range f)` (Restrict.lean:886)
- `MeasurableEmbedding.comap_map (mu) : (map f mu).comap f = mu` (Restrict.lean:899)
- `MeasurableEmbedding.subtype_coe (hs : MeasurableSet s)` (Restrict.lean:949)
- `MeasurableEquiv.measurableEmbedding`
- `OuterRegular.comap' (mu) (f_cont : Continuous f) (f_me : MeasurableEmbedding f)` (Regular.lean:402)
- `IsOpenPosMeasure.comap (mu) (hf : IsOpenEmbedding f)` (OpenPos.lean:153)
- `InnerRegularWRT.comap` (Regular.lean:262)
- `Measure.modularCharacterFun (g) : R>=0`; `modularCharacterFun_eq_haarScalarFactor (mu) [IsHaarMeasure mu] (g)`
  `: modularCharacterFun g = haarScalarFactor (map (.*g) mu) mu` (ModularCharacter.lean:57).
- `haarScalarFactor_self`, `map_right_mul_eq_modularCharacterFun_smul (needs InnerRegular)`.

## FIX (per instructions): no Homeomorph / no toContinuousLinearEquiv on Matrix (no norm).
Use `matrixToCoordMeasEquiv : Matrix =m coords` built from the Equiv + `continuous_of_finiteDimensional`
(norm free, already used at IwasawaHaar.lean:890 for `.symm`), compose with `subtype_coe` to get
`MeasurableEmbedding gToCoord`.

## Steps / commits  (PHASE 1 COMPLETE, all green, axiom clean)
1. [DONE] chart lemmas: `gToCoord`, `matrixToCoordMeasEquiv`, `measurableSet_det_ne_zero`,
   `measurableEmbedding_gToCoord`, `measurable_gToCoord`, `gToCoord_injective`,
   `leftMulCoord_matrixToCoord`, `rightMulCoord_matrixToCoord`, `gToCoord_leftMul`, `gToCoord_rightMul`.
2. [DONE] `nuG := Measure.comap gToCoord haarGCoord`; `range_gToCoord`, the two preimage range lemmas,
   `map_gToCoord_nuG`, `map_restrict_range_gToCoord_of_invariant`; `map_leftMul_nuG`, `map_rightMul_nuG`.
3. [DONE] chart topology norm free (`continuous_matrixToCoord`(_symm), `isOpenMap_matrixToCoord`,
   `continuous_gToCoord`, `isOpenMap_gToCoord`); `instIsMulLeftInvariant_nuG`,
   `instIsFiniteMeasureOnCompacts_nuG` (density bounded on chart image of a compact),
   `instIsOpenPosMeasure_nuG` (density positive on the invertible locus), `instIsHaarMeasure_nuG`.
4. [DONE] `modularCharacterFun_eq_one (g : G n) : modularCharacterFun g = 1`
   via `modularCharacterFun_eq_haarScalarFactor nuG g` + `map_rightMul_nuG` (simp, to dodge the
   dependent instance motive) + `haarScalarFactor_self`. Needed `import Mathlib.MeasureTheory.Group.ModularCharacter`.

## Optional / next (NOT done; reverted an attempt that needed unestablished regularity)
- `nuG = haarScalarFactor nuG haarG . haarG` by `isMulLeftInvariant_eq_smul_of_innerRegular`.
  Blocked: needs `InnerRegular nuG` and `InnerRegular haarG`, neither auto synthesizes here.
  To unblock: prove `SigmaCompactSpace (G n)` (second countable + locally compact), then
  `IsLocallyFiniteMeasure nuG` (from finite on compacts) gives `Regular nuG` via
  `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`, and `InnerRegular` via the
  `[InnerRegularCompactLTTop] [SigmaFinite] -> InnerRegular` instance; similarly for `haarG`.
  Note: this identification is NOT required for `modularCharacterFun = 1` (that uses measure
  independence of the modular character, so any explicit bi invariant Haar `nuG` suffices).

## PHASE 2 (Route B per factor Lebesgue to Haar) - not started this session
- `haarAExplicit` (A, log chart) and `nuU` (U, entry chart) already exist as explicit left Haar.
- Still needed: Cayley chart on K to `haarK`; assemble product `haarKAU` to `haarG` via the
  Iwasawa diffeomorphism and the Jacobian `2^{n(n-1)/2} |det a|^n |det adNN a|`.

STOP if a step needs an unprovable fact; never sorry/axiom; commit last green state.

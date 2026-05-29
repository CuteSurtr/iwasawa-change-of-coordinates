# haarG identification plan (branch `haar-identify`)

Goal: identify `haarGCoord` with `haarG` on `G n` and conclude
`Measure.modularCharacterFun (g : G n) = 1` (unimodularity of GL_n(R)).

## Ground truth (verified when this was written)
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

## Steps / commits
1. [build green -> commit] chart lemmas: `gToCoord`, `matrixToCoordMeasEquiv`, `measurableSet_det_ne_zero`,
   `measurableEmbedding_gToCoord`, `measurable_gToCoord`, `gToCoord_injective`,
   `leftMulCoord_matrixToCoord`, `rightMulCoord_matrixToCoord`, `gToCoord_leftMul`, `gToCoord_rightMul`.
2. [build green -> commit] `nuG := Measure.comap gToCoord haarGCoord`; left + right invariance (measure eqs).
3. [build green -> commit] `nuG` IsHaarMeasure + Regular (finite on compacts, open pos, left inv). HARD:
   likely needs `Continuous gToCoord` (Pi/finite-dim, norm free) and open-embedding for open pos.
   Range preservation: `range gToCoord = {w | (matrixToCoord.symm w).det != 0}`,
   preserved by `leftMulCoord g0.1` and `rightMulCoord g0.1` since det scales by det g0 != 0.
4. [build green -> commit] `modularCharacterFun g = 1` via `modularCharacterFun_eq_haarScalarFactor nuG g`
   + right invariance + `haarScalarFactor_self`. Optionally `nuG = c . haarG` by Haar uniqueness.

STOP if a step needs an unprovable fact; never sorry/axiom; commit last green state.

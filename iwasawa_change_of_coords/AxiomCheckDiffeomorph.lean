/-
Diagnostic file: axiom dependencies of the Stage T1-2 declarations
(bundling iwasawaEquiv as a Diffeomorph).

Current status: `iwasawaDiffeomorph` and `contMDiff_iwasawaSymm` are
proved without `sorryAx`; they should print only the standard
`[propext, Classical.choice, Quot.sound]` dependencies.
-/

import iwasawa_change_of_coords.IwasawaDiffeomorph

open IwasawaCoC

#print axioms IwasawaCoC.instChartedSpaceG_linfty
#print axioms IwasawaCoC.instIsManifoldG_linfty
#print axioms IwasawaCoC.instIsManifoldA_linfty
#print axioms IwasawaCoC.instIsManifoldUU_linfty
#print axioms IwasawaCoC.contDiff_cayley_subtype_val
#print axioms IwasawaCoC.aaProj
#print axioms IwasawaCoC.nnProj
#print axioms IwasawaCoC.contMDiff_K_subtypeVal
#print axioms IwasawaCoC.contMDiff_A_subtypeVal
#print axioms IwasawaCoC.contMDiff_UU_subtypeVal
#print axioms IwasawaCoC.contMDiff_iwasawaMap
#print axioms IwasawaCoC.contMDiff_iwasawaSymm
#print axioms IwasawaCoC.iwasawaDiffeomorph

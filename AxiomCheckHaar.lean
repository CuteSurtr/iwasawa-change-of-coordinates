/-
Diagnostic file: axiom dependencies of the measure layer (`IwasawaHaar.lean`):
the abstract factor Haar product, the explicit factor Haar measures, the
unimodularity of `GL_n(ℝ)`, the conjugation crux, the coordinate Haar measure,
and the three factor identifications. Each declaration should print only the
standard three axioms `[propext, Classical.choice, Quot.sound]`.
-/

import iwasawa_change_of_coords.IwasawaHaar

#print axioms IwasawaCoC.Complete.haarKAU
#print axioms IwasawaCoC.Complete.haarAExplicit
#print axioms IwasawaCoC.Complete.nuU
#print axioms IwasawaCoC.Complete.nuG
#print axioms IwasawaCoC.Complete.map_conjAut_haarN
#print axioms IwasawaCoC.Complete.modularCharacterFun_eq_one
#print axioms IwasawaCoC.Complete.nuG_eq_haarScalarFactor_smul_haarG
#print axioms IwasawaCoC.Complete.haarAExplicit_eq_haarScalarFactor_smul_haarA
#print axioms IwasawaCoC.Complete.nuU_eq_haarScalarFactor_smul_haarN
#print axioms IwasawaCoC.Complete.instIsHaarMeasure_nuG
#print axioms IwasawaCoC.Complete.instRegular_nuG
#print axioms IwasawaCoC.Complete.instIsHaarMeasure_nuU
#print axioms IwasawaCoC.Complete.instIsMulLeftInvariantHaarAExplicit

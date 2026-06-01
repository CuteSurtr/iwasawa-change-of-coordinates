/-
Diagnostic file: axiom dependencies of the K = O(n) Cayley chart Haar layer
(`IwasawaHaarK.lean`): the intrinsic chart derivative and its determinant pin,
the density `rhoK`, the candidate measure `nuK`, the Mobius left translation,
and the chart miss set reduction. Each declaration should print only the
standard three axioms `[propext, Classical.choice, Quot.sound]`.
-/

import iwasawa_change_of_coords.IwasawaHaarK

#print axioms IwasawaCoC.Complete.cayleyDerivOnSk
#print axioms IwasawaCoC.Complete.det_cayleyDerivOnSk
#print axioms IwasawaCoC.Complete.abs_det_cayleyDerivOnSk
#print axioms IwasawaCoC.Complete.rhoK
#print axioms IwasawaCoC.Complete.ofReal_abs_det_cayleyDerivOnSk
#print axioms IwasawaCoC.Complete.abs_det_cayleyDerivOnSk_two
#print axioms IwasawaCoC.Complete.continuous_rhoK
#print axioms IwasawaCoC.Complete.measurable_rhoK
#print axioms IwasawaCoC.Complete.volSk
#print axioms IwasawaCoC.Complete.nuK
#print axioms IwasawaCoC.Complete.measurable_cayleyToK
#print axioms IwasawaCoC.Complete.nuK_apply
#print axioms IwasawaCoC.Complete.cayleyLeftTrans
#print axioms IwasawaCoC.Complete.cayley_cayleyLeftTrans
#print axioms IwasawaCoC.Complete.cayleyToK_cayleyLeftTransSk
#print axioms IwasawaCoC.Complete.isOpen_cayleyLeftDom
#print axioms IwasawaCoC.Complete.continuousOn_cayleyLeftTrans
#print axioms IwasawaCoC.Complete.one_add_k_cayley_mul
#print axioms IwasawaCoC.Complete.det_one_add_k_cayley
#print axioms IwasawaCoC.Complete.mem_cayleyLeftDom_iff
#print axioms IwasawaCoC.Complete.nuK_eq_smul_haarK_of_invariant

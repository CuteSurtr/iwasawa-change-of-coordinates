/-
Diagnostic file: axiom dependencies of the Stage T1-3 declarations
(Theorems 1, 2, 3 for mfderiv at identity).

Current status: the Cartan involution derivative and the identity-point
Iwasawa derivative are proved without `sorryAx`; they should print only
the standard `[propext, Classical.choice, Quot.sound]` dependencies.
-/

import iwasawa_change_of_coords.IwasawaLieDecomposition
import iwasawa_change_of_coords.IwasawaMFDerivAtOne

open IwasawaCoC

#print axioms IwasawaCoC.iwasawaLieFamily
#print axioms IwasawaCoC.gl_decomposition_skew_diag_strictUpper
#print axioms IwasawaCoC.transposeCLM
#print axioms IwasawaCoC.negTransposeCLM
-- The sub-lemmas hasFDerivAt_ringInverse_one and
-- hasFDerivAt_cartanInvolutionExt_one are `private` in
-- IwasawaMFDerivAtOne.lean (intentional — they are reusable building
-- blocks for the open-submanifold bridge but not part of the public
-- API yet). They are verified at compile time.
#print axioms IwasawaCoC.cartanInvolution_mfderiv_one_eq_neg_transpose
#print axioms IwasawaCoC.iwasawaMap_mfderiv_at_one_eq_lieEquiv

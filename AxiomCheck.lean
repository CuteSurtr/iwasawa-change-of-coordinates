/-
Diagnostic file: print axiom dependencies of the main theorems.
Build with `lake build iwasawa_change_of_coords.AxiomCheck` and inspect
the output of the `#print axioms` commands.
-/

import iwasawa_change_of_coords.IwasawaCoC

open IwasawaCoC

#print axioms iwasawaEquiv
#print axioms inv_iwasawa_jl
#print axioms cartanInvolution_involutive
#print axioms cartanLieDecomp
#print axioms continuous_iwasawaMap
#print axioms isOpen_G
#print axioms G_isOpenEmbedding
#print axioms disjoint_AA_NN
#print axioms disjoint_KK_AA
#print axioms disjoint_KK_NN
#print axioms iwasawa_codisjoint
#print axioms iwasawaLieDecomp
#print axioms continuous_iwasawaSymm
#print axioms iwasawaHomeomorph
#print axioms iwasawaLieMap_surjective
#print axioms iwasawaLieMap_injective
#print axioms iwasawaLieEquiv
#print axioms IwasawaCoC.UU.toNNHomeomorph
#print axioms IwasawaCoC.instChartedSpaceUU
#print axioms IwasawaCoC.instIsManifoldUU
#print axioms IwasawaCoC.A.toFinNRHomeomorph
#print axioms IwasawaCoC.instChartedSpaceA
#print axioms IwasawaCoC.instIsManifoldA
#print axioms IwasawaCoC.one_add_skew_isUnit
#print axioms IwasawaCoC.cayley_isOrthogonal
#print axioms IwasawaCoC.cayleyToK
#print axioms IwasawaCoC.cayleyInv_cayley
#print axioms IwasawaCoC.cayley_cayleyInv
#print axioms IwasawaCoC.cayley_self_inverse
#print axioms IwasawaCoC.cayleyInv_isSkew
#print axioms IwasawaCoC.cayleyEquiv
#print axioms IwasawaCoC.continuous_cayley_on_skew
#print axioms IwasawaCoC.continuous_cayleyInv_on_KOpen
#print axioms IwasawaCoC.cayleyHomeomorph
#print axioms IwasawaCoC.instChartedSpaceKOpen
#print axioms IwasawaCoC.instIsManifoldKOpen
#print axioms IwasawaCoC.cayleyInv_isOpenEmbedding
#print axioms IwasawaCoC.contMDiff_cayleyHomeomorphSymm
#print axioms IwasawaCoC.contMDiff_cayleyHomeomorph
#print axioms IwasawaCoC.cayleyDiffeomorph
#print axioms IwasawaCoC.IsOrthogonal.mul
#print axioms IwasawaCoC.cayleyEquivAt
#print axioms IwasawaCoC.self_mem_K_open_at
#print axioms IwasawaCoC.cayleyOpenChartAt
#print axioms IwasawaCoC.cayleyOpenChartAt_source
#print axioms IwasawaCoC.instChartedSpaceK

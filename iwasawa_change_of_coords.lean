/-
Aggregate root for the `iwasawa_change_of_coords` library.

Importing this module pulls in every result of the development. `lake build`
uses it as the default target, so a clean clone compiles the whole library
with a single command.

The `AxiomCheck*` modules are deliberately excluded: they exist only to run
`#print axioms` on the headline theorems and are built explicitly, for example
`lake build iwasawa_change_of_coords.AxiomCheck`, so an ordinary build is not
flooded with their output.
-/

import iwasawa_change_of_coords.IwasawaBridge
import iwasawa_change_of_coords.IwasawaCoC
import iwasawa_change_of_coords.IwasawaComplete
import iwasawa_change_of_coords.IwasawaDiffeomorph
import iwasawa_change_of_coords.IwasawaHaar
import iwasawa_change_of_coords.IwasawaHaarK
import iwasawa_change_of_coords.IwasawaJacobianAbstract
import iwasawa_change_of_coords.IwasawaJacobianExplicit
import iwasawa_change_of_coords.IwasawaLieDecomposition
import iwasawa_change_of_coords.IwasawaMFDeriv
import iwasawa_change_of_coords.IwasawaMFDerivAtOne
import iwasawa_change_of_coords.IwasawaSmoothK
import iwasawa_change_of_coords.MatrixContDiff
import iwasawa_change_of_coords.PolynomialNullSet

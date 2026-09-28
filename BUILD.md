# Building

```bash
lake exe cache get   # prebuilt Mathlib; without it Mathlib compiles from source
lake build           # the whole library
```

Lean `v4.30.0-rc1` (`lean-toolchain`) and Mathlib at commit
`1708ec1fd9001d02aecb4bc71b70ca8690e4a894` (`lakefile.toml`,
`lake-manifest.json`). Without the cache, a clean build compiles about 2,500
Mathlib modules, which takes an hour or two on a 4-core machine.

## Why that Mathlib commit

It's the Mathlib pinned by the Iwasawa_Decomposition repository, which is the
Lake project this code was developed in (it used to be a subdirectory there and
shared that project's configuration). When this repository got its own build
configuration, it was pinned to the `v4.30.0-rc1` tag instead. The tag uses the
same toolchain but is 368 commits older, and on it `IwasawaCoC.lean` failed to
elaborate with 15 errors, starting with
`failed to synthesize ChartedSpace (↥(Sk n)) (K_open n)`: instance search didn't
find the `ChartedSpace` instances on the model spaces `Sk n` and `NN n`. On
`1708ec1f` the same file elaborates without changes.

## Layout

Module names are resolved from the package root:

| Module | File |
|---|---|
| `project.Iwasawa` | `project/Iwasawa.lean` |
| `iwasawa_change_of_coords.X` | `iwasawa_change_of_coords/X.lean` |
| `iwasawa_change_of_coords` | `iwasawa_change_of_coords.lean` |

`lake build` builds the root module `iwasawa_change_of_coords.lean`, which imports
everything except the `AxiomCheck*` files.

`project/Iwasawa.lean` is the decomposition $`g = kau`$ itself, vendored from the
Iwasawa_Decomposition repository. It's an older version than the one published
there: upstream commit `4465bdd` removed `IsOrthogonal.transpose` and
`IsOrthogonal.matInv_eq_transpose`, and this project uses both. To re-sync the
two, either restore those lemmas upstream or move them into this repository.

## Axiom checks

`IwasawaIntegration.lean` ends with `#print axioms` for its ten main results
wrapped in `#guard_msgs`, so `lake build` fails if any of them ever depends on
`sorryAx` or on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. `IwasawaBridge`, `IwasawaComplete`, `IwasawaHaar`, `IwasawaHaarK` and
`PolynomialNullSet` end with plain `#print axioms` blocks, whose output shows up in
the build log. The eight `AxiomCheck*.lean` files contain 120 more and are built
on request:

```bash
lake build iwasawa_change_of_coords.AxiomCheck
lake build iwasawa_change_of_coords.AxiomCheckDiffeomorph
lake build iwasawa_change_of_coords.AxiomCheckHaar
lake build iwasawa_change_of_coords.AxiomCheckHaarK
lake build iwasawa_change_of_coords.AxiomCheckMFDeriv
lake build iwasawa_change_of_coords.AxiomCheckMFDerivAtOne
lake build iwasawa_change_of_coords.AxiomCheckPolynomialNullSet
lake build iwasawa_change_of_coords.AxiomCheckSmoothK
```

CI (`.github/workflows/build.yml`) runs `lake build` through
`leanprover/lean-action` on pushes to `main` and on pull requests.

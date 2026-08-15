# Building

```bash
lake exe cache get   # prebuilt Mathlib oleans; avoids a multi-hour local build
lake build project   # the base Iwasawa decomposition
lake build           # the full library
```

Toolchain `leanprover/lean4:v4.30.0-rc1`, Mathlib pinned to `v4.30.0-rc1`.

## Layout

Module names are resolved from the package root, which is what the existing
`import` lines assume:

| Module | File |
|---|---|
| `project.Iwasawa` | `project/Iwasawa.lean` |
| `iwasawa_change_of_coords.X` | `iwasawa_change_of_coords/X.lean` |
| `iwasawa_change_of_coords` | `iwasawa_change_of_coords.lean` (aggregate root) |

`project/Iwasawa.lean` is the base Iwasawa decomposition, **vendored** rather
than pulled from the companion `Iwasawa_Decomposition` repository. That is
deliberate: the published version of that file has had `IsOrthogonal.transpose`
removed, and this development still depends on it, so pulling the current
upstream copy does not compile. The two should be re-synchronised at some
point; until then the vendored copy is the one this library is known to build
against.

The `AxiomCheck*` modules are excluded from the aggregate root because they
exist only to run `#print axioms`. Build them explicitly when you want that
audit:

```bash
lake build iwasawa_change_of_coords.AxiomCheck
```

## Current status

| Target | State |
|---|---|
| `project.Iwasawa` | **builds**, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) |
| `iwasawa_change_of_coords.MatrixContDiff` | **builds** |
| `iwasawa_change_of_coords.PolynomialNullSet` | **builds** |
| `iwasawa_change_of_coords.IwasawaCoC` | **15 errors**, all one root cause (below) |
| everything downstream of `IwasawaCoC` | blocked by the above |

There are **no `sorry`s or `admit`s** anywhere in the sources. The failures are
elaboration errors, not proof holes.

## The open issue: a topology diamond on the submodule model spaces

`Sk n` and `NN n` are `Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)`, so `↥(Sk n)`
carries two *different terms* for the same topology:

- `instTopologicalSpaceSubtype`, which is what instance search returns, and
  what the `ChartedSpace` instances in this file are built over;
- the one reached through `Submodule.normedAddCommGroup` →
  `SeminormedAddCommGroup` → `PseudoMetricSpace` → `UniformSpace` →
  `TopologicalSpace`, which is what `𝓘(ℝ, Sk n)` fixes.

A manifold statement therefore asks for a `ChartedSpace` at the *model's*
topology and does not find the one declared at the subtype topology. The
reported errors are

```
failed to synthesize   ChartedSpace (↥(Sk n)) (K_open n)
failed to synthesize   ChartedSpace ↥(Sk n) ↥(Sk n)
```

and the `Unknown identifier n` errors are cascade: when a statement fails to
elaborate, the section's `variable {n}` is never bound for its body.

**The two topologies are definitionally equal.** This typechecks:

```lean
example (m : ℕ) :
    (inferInstance : TopologicalSpace ↥(Sk m))
      = (inferInstanceAs (NormedAddCommGroup ↥(Sk m))).toSeminormedAddCommGroup
          .toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := rfl
```

So this is a syntactic instance-search failure, not an incoherence, and
bridging it is sound.

### What is already fixed

`instIsManifoldUU` and `instIsManifoldKOpen` are now stated with the charted
space given **explicitly**, following Mathlib's own `isManifold_singleton`,
whose conclusion is `@IsManifold 𝕜 _ E _ _ H _ I n M _ (e.singletonChartedSpace h)`.
Naming the instance moves the burden from instance search to defeq checking,
which succeeds. That removed three of the original errors.

### What remains

The `ContMDiff` / `Diffeomorph` statements over these model spaces need the
same treatment. They take their charted spaces through section `variable`s, so
the `@` form is unwieldy; the better fix is probably to remove the ambiguity at
the source so only one topology term is ever in scope, for example by giving
`Sk n` and `NN n` a single canonical normed structure rather than relying on
the `Submodule` coercion. That is a structural decision about the development,
which is why it has been left rather than guessed at.

Building on Mathlib `v4.30.0` final instead of `v4.30.0-rc1` adds three further
errors, all in the same area; the manifold library was refactored between the
two.

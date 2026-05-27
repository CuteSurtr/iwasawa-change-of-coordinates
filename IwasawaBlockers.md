# Current Blockers and Status

This file is a current status note for the Iwasawa change-of-coordinates
project. Older status logs have been superseded by the proved
diffeomorphism and derivative layers.

## Verified Core Status

- `lake build` succeeds from the parent Lake project root.
- The namespace for the project declarations is `IwasawaCoC`.
- `IwasawaCoC.contMDiff_iwasawaSymm` depends only on
  `[propext, Classical.choice, Quot.sound]`.
- `IwasawaCoC.iwasawaDiffeomorph` depends only on
  `[propext, Classical.choice, Quot.sound]`.
- `IwasawaCoC.mfderiv_iwasawaMap_at_factored` depends only on
  `[propext, Classical.choice, Quot.sound]`.
- There are no active Lean `sorry` declarations in
  `iwasawa_change_of_coords/`.

## Derivative Layer

The general derivative theorem is closed:

```lean
IwasawaCoC.mfderiv_iwasawaMap_at_factored
```

Its right-hand side is the direct chart-level matrix Leibniz map

```lean
iwasawaMatrixLeibnizCLM k a u
```

This is the actual derivative of `iwasawaMap` in the current charts.
The Cayley chart convention contributes the `-2` factor on the `K`
component.

The older

```lean
lieTwistCLM a
```

is retained as an auxiliary source twist. It is useful for isolating the
`A`-action on `NN` and for recognizing the positive-root density factor,
but it is not the full derivative of `iwasawaMap` in the current chart
convention.

## Jacobian Layer

`IwasawaJacobianExplicit.lean` proves the explicit determinant formula

```lean
adNN_det_eq_pair_product
```

which computes

```text
det(adNN a) = ∏_{i<j} a_i / a_j.
```

This is the positive-root product expected in the Iwasawa measure
formula. The remaining Stage 4 work is to connect this auxiliary
determinant to the determinant of the actual derivative
`iwasawaMatrixLeibnizCLM k a u`, with the relevant chart constants made
explicit.

## Quarantined Haar Bridge

`IwasawaBridge.lean` is future Haar/change-of-variables scaffolding.
It still contains one explicit axiom:

```lean
iwasawa_haar_pushforward_bridge
```

That axiom should not be counted as part of the axiom-clean
diffeomorphism or derivative core. A real replacement should eventually
state a measure-theoretic pushforward or integral formula using product
measures, Haar measures, and a proved Jacobian theorem.

## Current Conservative Next Step

Do not attempt the full Haar theorem yet. The next implementation stage
should be a small determinant-facing step:

1. State a basis-level determinant theorem for
   `iwasawaMatrixLeibnizCLM k a u`.
2. Relate its `A`-dependent part to `adNN_det_eq_pair_product`.
3. Keep `IwasawaBridge.lean` quarantined until the chart-level
   determinant theorem is in place.

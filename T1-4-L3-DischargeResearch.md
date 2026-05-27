# Superseded T1-4 L3 Research Note

This note has been superseded by the completed proof of
`IwasawaCoC.mfderiv_iwasawaMap_at_factored`.

Current status:

- The theorem builds directly from the chart-level matrix derivative
  calculation.
- Its right-hand side is `iwasawaMatrixLeibnizCLM k a u`.
- The declaration prints only `[propext, Classical.choice, Quot.sound]`.
- The older bridge-axiom route is no longer used for this derivative
  theorem.

The remaining Stage 4 work is determinant-facing: prove a clean
basis-level determinant theorem for `iwasawaMatrixLeibnizCLM k a u` and
then connect its `A`-dependent part to `adNN_det_eq_pair_product`.

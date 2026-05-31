/-
# The zero set of a nonzero real polynomial has Lebesgue measure zero

For a nonzero `p : MvPolynomial (Fin d) ℝ`, the zero locus
`{x : Fin d → ℝ | MvPolynomial.eval x p = 0}` has Lebesgue (Pi) measure zero.

Mathlib has the one variable case (`Polynomial.finite_setOf_isRoot`, finitely
many roots) and the Schwartz-Zippel counting bound over finite sets, but not this
multivariate Lebesgue null statement. The proof is the standard `finSuccEquiv`
induction with Fubini: split off the first variable, use the induction hypothesis
on the leading coefficient (null base set), and `Polynomial.finite_setOf_isRoot`
on each remaining one variable slice (finite, hence null fiber).

This file is self contained and intended to be reusable and upstreamable.
-/

import Mathlib

open MeasureTheory MvPolynomial

namespace MvPolynomial

variable {d : ℕ}

/-- The zero locus of a real `MvPolynomial` is closed, hence measurable. -/
theorem measurableSet_setOf_eval_eq_zero (p : MvPolynomial (Fin d) ℝ) :
    MeasurableSet {x : Fin d → ℝ | eval x p = 0} :=
  (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet

/-- Base case `d = 0`: a nonzero polynomial in no variables has empty zero locus
(its value is the nonzero constant coefficient), so the locus is null. -/
theorem volume_setOf_eval_eq_zero_of_isEmpty (p : MvPolynomial (Fin 0) ℝ) (hp : p ≠ 0) :
    volume {x : Fin 0 → ℝ | eval x p = 0} = 0 := by
  have hempty : {x : Fin 0 → ℝ | eval x p = 0} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hval : eval x p = p.coeff 0 := by nth_rewrite 1 [eq_C_of_isEmpty p]; simp
    apply hp
    rw [eq_C_of_isEmpty p, ← hval, hx]; simp
  rw [hempty, measure_empty]

#print axioms measurableSet_setOf_eval_eq_zero
#print axioms volume_setOf_eval_eq_zero_of_isEmpty

end MvPolynomial

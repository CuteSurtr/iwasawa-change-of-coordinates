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

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.MvPolynomial

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

/-- **The Mathlib gap.** The zero locus of a nonzero real polynomial in finitely
many variables has Lebesgue (Pi) measure zero.

Induction on the number of variables. The base case is
`volume_setOf_eval_eq_zero_of_isEmpty`. For the step, `finSuccEquiv` views `p` as
a one variable polynomial `q` over `MvPolynomial (Fin d) ℝ`; its leading
coefficient is nonzero, so by the induction hypothesis the base locus
`{s | eval s q.leadingCoeff = 0}` is null. Off that null set the one variable
slice is a nonzero polynomial, with finitely many (hence null) roots. Fubini
(`measure_prod_null`) over the tail/head product then gives the result. -/
theorem volume_setOf_eval_eq_zero :
    ∀ {d : ℕ} (p : MvPolynomial (Fin d) ℝ), p ≠ 0 →
      volume {x : Fin d → ℝ | eval x p = 0} = 0 := by
  intro d
  induction d with
  | zero => exact fun p hp => volume_setOf_eval_eq_zero_of_isEmpty p hp
  | succ d ih =>
    intro p hp
    have hq0 : finSuccEquiv ℝ d p ≠ 0 := fun h => hp (by
      have h2 := congrArg (finSuccEquiv ℝ d).symm h; simpa using h2)
    have hc0 : (finSuccEquiv ℝ d p).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hq0
    have hFcont : Continuous fun sy : (Fin d → ℝ) × ℝ => eval (Fin.cons sy.2 sy.1) p := by
      refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_snd
      · simpa using (continuous_apply j).comp continuous_fst
    have hS' : MeasurableSet {sy : (Fin d → ℝ) × ℝ | eval (Fin.cons sy.2 sy.1) p = 0} :=
      (isClosed_eq hFcont continuous_const).measurableSet
    have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0)
        (volume : Measure (Fin (d + 1) → ℝ)) volume :=
      volume_preserving_piFinSuccAbove (fun _ => ℝ) 0
    have hvolZ : volume {x : Fin (d + 1) → ℝ | eval x p = 0}
        = volume {ys : ℝ × (Fin d → ℝ) | eval (Fin.cons ys.1 ys.2) p = 0} := by
      rw [← he.symm.measure_preimage (measurableSet_setOf_eval_eq_zero p).nullMeasurableSet]
      congr 1
      ext ys
      simp only [Set.mem_preimage, Set.mem_setOf_eq,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
      rfl
    have hswapeq : {ys : ℝ × (Fin d → ℝ) | eval (Fin.cons ys.1 ys.2) p = 0}
        = Prod.swap ⁻¹' {sy : (Fin d → ℝ) × ℝ | eval (Fin.cons sy.2 sy.1) p = 0} := by
      ext ys; simp [Prod.swap]
    rw [hvolZ, hswapeq]
    show ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ)))
        (Prod.swap ⁻¹' {sy : (Fin d → ℝ) × ℝ | eval (Fin.cons sy.2 sy.1) p = 0}) = 0
    rw [(Measure.measurePreserving_swap).measure_preimage hS'.nullMeasurableSet,
      Measure.measure_prod_null hS']
    show ∀ᵐ s ∂(volume : Measure (Fin d → ℝ)),
        volume (Prod.mk s ⁻¹' {sy : (Fin d → ℝ) × ℝ | eval (Fin.cons sy.2 sy.1) p = 0}) = 0
    rw [ae_iff]
    refine measure_mono_null ?_ (ih (finSuccEquiv ℝ d p).leadingCoeff hc0)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    by_contra hsc
    apply hs
    have hslice : Prod.mk s ⁻¹' {sy : (Fin d → ℝ) × ℝ | eval (Fin.cons sy.2 sy.1) p = 0}
        = {y : ℝ | eval (Fin.cons y s) p = 0} := by
      ext y; simp
    rw [hslice]
    have hmap : (finSuccEquiv ℝ d p).map (eval s) ≠ 0 := by
      intro h
      apply hsc
      show eval s ((finSuccEquiv ℝ d p).coeff (finSuccEquiv ℝ d p).natDegree) = 0
      rw [← Polynomial.coeff_map, h, Polynomial.coeff_zero]
    have hfin : {y : ℝ | eval (Fin.cons y s) p = 0}.Finite := by
      have heq : {y : ℝ | eval (Fin.cons y s) p = 0}
          = {y : ℝ | ((finSuccEquiv ℝ d p).map (eval s)).IsRoot y} := by
        ext y; simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, eval_eq_eval_mv_eval']
      rw [heq]; exact Polynomial.finite_setOf_isRoot hmap
    exact hfin.measure_zero _

#print axioms measurableSet_setOf_eval_eq_zero
#print axioms volume_setOf_eval_eq_zero_of_isEmpty
#print axioms volume_setOf_eval_eq_zero

end MvPolynomial

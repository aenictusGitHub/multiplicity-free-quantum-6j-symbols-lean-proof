import SpinRacahPhysicalFormula
import SpinRacahFactorialSum
import SpinRacahEndpointFactorial
import QuantumGaugeClosed
import QuantumLeadingRegular
import QuantumFirstChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def physicalRacahClosedPrefactor (q : ℝ) (l m n H : ℕ)
    (first p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) : ℝ :=
  (boundaryRacahNormalization q l m n first.val a*boundaryRacahRaw q l m n first.val a/
    spinRacahEndpointFactorial q m n (leftHighestDefect l m n H) a.1.val)*
    (regularProjectedLeading q l m n p.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) p.val/
      (regularProjectedLeading q l m n first.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) first.val))*
    spinRacahFactorialConstant q l m n (leftHighestDefect l m n H) a.1.val p.val.1.val p.val.2.val

theorem searsFactorialConstant_pos (q : ℝ) (hq : 0<q) (u r A B M S T : ℕ) :
    0<searsFactorialConstant q u r A B M S T := by
  exact div_pos
    (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))
      (qfactorial_pos q hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (qfactorial_pos q hq _)

theorem spinRacahFactorialConstant_pos (q : ℝ) (hq : 0<q) (l m n R u r s : ℕ) :
    0<spinRacahFactorialConstant q l m n R u r s := by
  exact div_pos
    (mul_pos (mul_pos (searsFactorialConstant_pos q hq _ _ _ _ _ _ _) (qfactorial_pos q hq _))
      (qfactorial_pos q hq _))
    (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))

theorem physicalRacahClosedPrefactor_pos (q : ℝ) (hq : 0<q) (l m n H : ℕ)
    (first p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) :
    0<physicalRacahClosedPrefactor q l m n H first p a := by
  exact mul_pos
    (mul_pos (div_pos (mul_pos (boundaryRacahNormalization_pos q hq _ _ _ _ _)
      (boundaryRacahRaw_pos q hq _ _ _ _ _)) (spinRacahEndpointFactorial_pos q hq _ _ _ _))
      (div_pos (mul_pos (regularProjectedLeading_pos q hq _ _ _ _)
        (projectedGaugeFactor_pos q hq _ _ _ _ _))
        (mul_pos (regularProjectedLeading_pos q hq _ _ _ _)
          (projectedGaugeFactor_pos q hq _ _ _ _ _))))
    (spinRacahFactorialConstant_pos q hq _ _ _ _ _ _ _)

/-- Independently constructed physical rank-two recoupling is a single Racah
quantum-factorial sum with a closed, positive factorial normalization.
No hypergeometric sum or finite gauge product remains in the prefactor. -/
theorem quantumRacahMatrix_closed_factorial_sum (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n H : ℕ) (first : FixedLeftHighest l m n H)
    (hb : first.val.1.val=0 ∨ first.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    ∀ p : FixedLeftHighest l m n H,
      quantumRacahMatrix q hq hq1 l m n p.val a=physicalRacahClosedPrefactor q l m n H first p a*
        spinRacahFactorialSum q l m n (leftHighestDefect l m n H) a.1.val p.val.1.val p.val.2.val := by
  intro p
  have hadm := rightHighest_spinRacah_admissible l m n H a hH
  have hd := fixedLeftHighest_defect l m n H p
  rw [quantumRacahMatrix_terminating_four_phi_three q hq hq1 l m n H first hb a hH p]
  unfold spinRacahPhysicalFormula
  rw [spinRacahGauge_closed q hq hq1 l m n H first hb p,
    projectedLeftLeading_regular q hq hq1 l m n p.val,
    projectedLeftLeading_regular q hq hq1 l m n first.val,
    spinRacah_lower_endpoint_factorial q hq hq1 l m n (leftHighestDefect l m n H) a.1.val hadm,
    spinRacahFunction_factorial_sum q hq hq1 l m n (leftHighestDefect l m n H) a.1.val
      p.val.1.val p.val.2.val hadm (channel_right_bound l m p.val.1)
      (channel_right_bound (coupledLabel l m p.val.1) n p.val.2) hd]
  unfold physicalRacahClosedPrefactor
  ring

/-- The required initial row always exists in each nonempty physical block. -/
theorem quantumRacahMatrix_factorial_block (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n H : ℕ) (p₀ : FixedLeftHighest l m n H)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    ∃ first : FixedLeftHighest l m n H,(first.val.1.val=0 ∨ first.val.2.val=n) ∧
      ∀ p : FixedLeftHighest l m n H,
        quantumRacahMatrix q hq hq1 l m n p.val a=physicalRacahClosedPrefactor q l m n H first p a*
          spinRacahFactorialSum q l m n (leftHighestDefect l m n H) a.1.val p.val.1.val p.val.2.val := by
  obtain ⟨first,hb⟩ := fixedLeftHighest_first_exists l m n H p₀
  exact ⟨first,hb,quantumRacahMatrix_closed_factorial_sum q hq hq1 l m n H first hb a hH⟩

end AMSPhysical

#print axioms AMSPhysical.quantumRacahMatrix_closed_factorial_sum
#print axioms AMSPhysical.quantumRacahMatrix_factorial_block

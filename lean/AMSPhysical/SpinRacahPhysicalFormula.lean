import SpinRacahPhysicalEigenvector
import QuantumRacahUniqueness

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Purely scalar terminating 4phi3 evaluation, with an explicit factorial
boundary factor and a finite product of quantum-integer square roots. -/
def spinRacahPhysicalFormula (q : ℝ) (l m n H : ℕ)
    (first p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) : ℝ :=
  (boundaryRacahNormalization q l m n first.val a*boundaryRacahRaw q l m n first.val a/
    spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val
      ((leftHighestDefect l m n H-n:ℕ):ℤ))*
    (spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val*
      spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val p.val.1.val)

/-- The terminating basic hypergeometric expression equals the overlap of the
actual isometric Uq(sl2) Clebsch-Gordan trees. No physical-identification
hypothesis or conjectural formula is used. -/
theorem quantumRacahMatrix_terminating_four_phi_three (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n H : ℕ) (first : FixedLeftHighest l m n H)
    (hbound : first.val.1.val=0 ∨ first.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    ∀ p : FixedLeftHighest l m n H,
      quantumRacahMatrix q hq hq1 l m n p.val a=spinRacahPhysicalFormula q l m n H first p a := by
  classical
  have hrec := spinRacah_physical_eigenvector q hq hq1 l m n H a hH
  have hadm := rightHighest_spinRacah_admissible l m n H a hH
  have hnonzero := spinRacah_lower_endpoint_nonzero (q^2) (sq_pos_of_pos hq)
    (quantum_square_base_ne_one q hq hq1) l m n (leftHighestDefect l m n H) a.1.val hadm
  have hidx := fixedLeftHighest_boundary_index l m n H first hbound
  have he := quantumRacah_factorial_initial_unique q hq hq1 l m n H first hbound a hH
    (fun p => spinRacahPhysicalFormula q l m n H first p a) ?_ ?_
  · exact fun p => (he p).symm
  · intro p
    dsimp only
    unfold spinRacahPhysicalFormula
    calc
      _ = (boundaryRacahNormalization q l m n first.val a*boundaryRacahRaw q l m n first.val a/
          spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val
            ((leftHighestDefect l m n H-n:ℕ):ℤ))*
          (∑ v,quantumRacahJacobi q hq hq1 l m n H p v*
            (spinRacahGauge q l m n (leftHighestDefect l m n H) v.val.1.val*
              spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val v.val.1.val)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [hrec p];ring
  · dsimp only
    unfold spinRacahPhysicalFormula
    have hg : spinRacahGauge q l m n (leftHighestDefect l m n H) first.val.1.val=1 := by
      rw [hidx,spinRacahGauge_first]
    rw [hg,one_mul]
    have hx : spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val first.val.1.val=
      spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val
        ((leftHighestDefect l m n H-n:ℕ):ℤ) := by
      congr 1
      omega
    rw [hx,div_mul_cancel₀ _ hnonzero]

end AMSPhysical

#print axioms AMSPhysical.quantumRacahMatrix_terminating_four_phi_three

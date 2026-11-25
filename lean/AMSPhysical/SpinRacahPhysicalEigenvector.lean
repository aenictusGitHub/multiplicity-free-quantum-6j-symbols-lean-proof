import SpinRacahScale
import SpinRacahGauge
import QuantumDiagonalRates
import FiniteGridEigenvector

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The explicitly normalized terminating 4phi3 is an eigenvector of the
actual physical intermediate Casimir, at every admissible channel. -/
theorem spinRacah_physical_eigenvector (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    ∀ p : FixedLeftHighest l m n H,
      (∑ v,quantumRacahJacobi q hq hq1 l m n H p v*
        (spinRacahGauge q l m n (leftHighestDefect l m n H) v.val.1.val*
          spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val v.val.1.val))=
      quantumCasimirEigen q (coupledLabel m n a.1)*
        (spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val*
          spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val p.val.1.val) := by
  classical
  have hadm := rightHighest_spinRacah_admissible l m n H a hH
  apply finite_grid_eigenvector (quantumRacahJacobi q hq hq1 l m n H)
    (fun p => p.val.1.val) (fixedLeftHighest_index_injective l m n H)
    (fun p => spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val)
    (fun p => sl2RacahBirth q l m n p.val.1.val p.val.2.val)
    (fun p => sl2RacahDeath q l m n p.val.1.val p.val.2.val)
    (spinRacahFunction (q^2) l m n (leftHighestDefect l m n H) a.1.val)
    (quantumCasimirEigen q ((m:ℤ)+(n:ℤ))) (quantumCasimirEigen q (coupledLabel m n a.1))
  · exact quantumRacahJacobi_diagonal_birth_death q hq hq1 l m n H
  · intro p v hv
    exact (spinRacahGauge_death q hq hq1 l m n H p v hv).symm
  · intro p v hv
    rw [quantumRacahJacobi_symmetric q hq hq1 l m n H p v]
    exact spinRacahGauge_birth q hq hq1 l m n H v p hv
  · intro p v hm hp hne
    have hindex : p.val.1.val≠v.val.1.val := fun he => hne (fixedLeftHighest_index_injective l m n H he)
    exact quantumRacahJacobi_tridiagonal q hq hq1 l m n H p v (by omega)
  · intro p hp
    rw [sl2RacahDeath_lower_boundary q l m n H p hp,zero_mul]
  · intro p hp
    exact spinRacah_upper_boundary (q^2) (sq_pos_of_pos hq) (quantum_square_base_ne_one q hq hq1)
      q l m n H a.1.val hadm p hp
  · intro p
    have hr := fixedLeftHighest_defect l m n H p
    have hc := spinRacahFunction_physical_difference q hq hq1 l m n (leftHighestDefect l m n H)
      a.1.val p.val.1.val p.val.2.val hadm
      (channel_left_bound l m p.val.1) (channel_right_bound l m p.val.1)
      (channel_left_bound (coupledLabel l m p.val.1) n p.val.2) hr
    rw [coupledLabel_cast m n a.1.val (channel_left_bound m n a.1) (channel_right_bound m n a.1)]
    exact hc

end AMSPhysical

#print axioms AMSPhysical.spinRacah_physical_eigenvector

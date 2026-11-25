import QuantumJacobiEightFactors
import QuantumRacahUniqueness

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- A fully explicit quantum-number recurrence matrix, independent of physical intertwiner maps. -/
def explicitQuantumJacobi (q : ℝ) (l m n H : ℕ) (p v : FixedLeftHighest l m n H) : ℝ := by
  classical
  exact if p=v then casimirJacobiDiagonalClosed q l m n p.val else
    if v.val.1.val+1=p.val.1.val then Real.sqrt (casimirJacobiNeighborSquare q l m n p.val) else
      if p.val.1.val+1=v.val.1.val then Real.sqrt (casimirJacobiNeighborSquare q l m n v.val) else 0

theorem quantumRacahJacobi_explicit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) :
    quantumRacahJacobi q hq hq1 l m n H p v=explicitQuantumJacobi q l m n H p v := by
  classical
  unfold explicitQuantumJacobi
  by_cases hpv : p=v
  · subst v
    rw [if_pos rfl]
    exact quantumRacahJacobi_diagonal q hq hq1 l m n H p
  · rw [if_neg hpv]
    by_cases hnext : v.val.1.val+1=p.val.1.val
    · rw [if_pos hnext]
      exact quantumRacahJacobi_step_sqrt q hq hq1 l m n H p v hnext
    · rw [if_neg hnext]
      by_cases hprev : p.val.1.val+1=v.val.1.val
      · rw [if_pos hprev,quantumRacahJacobi_symmetric q hq hq1 l m n H p v]
        exact quantumRacahJacobi_step_sqrt q hq hq1 l m n H v p hprev
      · rw [if_neg hprev]
        have hne : p.val.1.val≠v.val.1.val := fun h => hpv (fixedLeftHighest_index_injective l m n H h)
        exact quantumRacahJacobi_tridiagonal q hq hq1 l m n H p v (by omega)

/-- A pure scalar recurrence and factorial boundary value uniquely recover the actual
rank-two physical recoupling column; its hypotheses contain no physical overlap. -/
theorem quantumRacah_explicit_recurrence_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (first : FixedLeftHighest l m n H) (hbound : first.val.1.val=0 ∨ first.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H)
    (f : FixedLeftHighest l m n H → ℝ)
    (hf : ∀ p,(∑ v,explicitQuantumJacobi q l m n H p v*f v)=
      quantumCasimirEigen q (coupledLabel m n a.1)*f p)
    (hfirst : f first=boundaryRacahNormalization q l m n first.val a*boundaryRacahRaw q l m n first.val a) :
    ∀ p,f p=quantumRacahMatrix q hq hq1 l m n p.val a := by
  apply quantumRacah_factorial_initial_unique q hq hq1 l m n H first hbound a hH f
  · intro p
    simpa only [quantumRacahJacobi_explicit q hq hq1 l m n H] using hf p
  · exact hfirst

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_explicit
#print axioms AMSPhysical.quantumRacah_explicit_recurrence_unique

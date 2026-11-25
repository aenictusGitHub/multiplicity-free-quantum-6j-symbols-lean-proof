import QuantumBoundaryFormula
import JacobiEigenvectorUniqueness

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- All nonextremal physical channels have a nonzero preceding Jacobi entry. -/
theorem quantumRacahJacobi_connected (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (first : FixedLeftHighest l m n H) (hbound : first.val.1.val=0 ∨ first.val.2.val=n)
    (p : FixedLeftHighest l m n H) (hp : p≠first) :
    ∃ v : FixedLeftHighest l m n H,v.val.1.val+1=p.val.1.val ∧ quantumRacahJacobi q hq hq1 l m n H v p≠0 := by
  have hnbound : ¬(p.val.1.val=0 ∨ p.val.2.val=n) := by
    intro hb
    apply hp
    apply fixedLeftHighest_index_injective l m n H
    have h₁ := fixedLeftHighest_boundary_minimal l m n H first hbound p
    have h₂ := fixedLeftHighest_boundary_minimal l m n H p hb first
    change p.val.1.val=first.val.1.val
    omega
  have hr : 0<p.val.1.val := by omega
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hs : p.val.2.val<n := by omega
  obtain ⟨v,hv⟩ := fixedLeftHighest_previous l m n H p hr hs
  refine ⟨v,hv,?_⟩
  rw [quantumRacahJacobi_symmetric q hq hq1 l m n H v p]
  exact ne_of_gt (quantumRacahJacobi_step_pos q hq hq1 l m n H p v hv)

/-- The actual recoupling column is uniquely fixed by its physical recurrence
and the independently evaluated boundary factorial coefficient. -/
theorem quantumRacah_factorial_initial_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (first : FixedLeftHighest l m n H) (hbound : first.val.1.val=0 ∨ first.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H)
    (f : FixedLeftHighest l m n H → ℝ)
    (hf : ∀ p,(∑ v,quantumRacahJacobi q hq hq1 l m n H p v*f v)=
      quantumCasimirEigen q (coupledLabel m n a.1)*f p)
    (hfirst : f first=boundaryRacahNormalization q l m n first.val a*boundaryRacahRaw q l m n first.val a) :
    ∀ p,f p=quantumRacahMatrix q hq hq1 l m n p.val a := by
  classical
  have he := tridiagonal_eigenvector_unique (quantumRacahJacobi q hq hq1 l m n H)
    (fun p => p.val.1.val) (fixedLeftHighest_index_injective l m n H) first
    (fun p v hpv => quantumRacahJacobi_tridiagonal q hq hq1 l m n H p v (Or.inr hpv))
    (quantumRacahJacobi_connected q hq hq1 l m n H first hbound)
    f (fun p => quantumRacahMatrix q hq hq1 l m n p.val a) (quantumCasimirEigen q (coupledLabel m n a.1))
    hf (fun p => quantumRacah_Casimir_recurrence q hq hq1 l m n H p a)
    (hfirst.trans (quantumRacah_boundary_factorial q hq hq1 l m n H first hbound a hH).symm)
  exact fun p => congrFun he p

end AMSPhysical

#print axioms AMSPhysical.quantumRacah_factorial_initial_unique

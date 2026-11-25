import JacobiDiagonalAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 6000000
noncomputable section
namespace AMSPhysical

/-- The zero intermediate-spin endpoint, where the forward coefficient has
its total-division value zero, obeys the same physical diagonal formula. -/
theorem casimir_diagonal_rational_zero (q X N : ℝ) (hq : q≠0) (hX : X≠0) (hN : N≠0)
    (hD : q^2-1≠0) (hP : q^2+1≠0) :
    (q-q⁻¹)^2*symmetricQNumber q X*N+q*N/X+X/(q*N)+
      (q-q⁻¹)^2/q^2*symmetricQNumber q X*symmetricQNumber q N/symmetricQNumber q (q^2)=
      q*X*N+(q*X*N)⁻¹-
        (q-q⁻¹)^2*symmetricQNumber q X*symmetricQNumber q N/symmetricQNumber q (q^2) := by
  have h4 : q^4-1≠0 := by
    have hp : q^4-1=(q^2-1)*(q^2+1) := by ring
    rw [hp]
    exact mul_ne_zero hD hP
  unfold symmetricQNumber
  field_simp [hq,hX,hN,hD,hP,h4] <;> ring

end AMSPhysical

#print axioms AMSPhysical.casimir_diagonal_rational_zero

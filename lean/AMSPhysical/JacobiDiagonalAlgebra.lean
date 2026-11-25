import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def symmetricQNumber (q x : ℝ) : ℝ := (x-x⁻¹)/(q-q⁻¹)

/-- Rational polynomial certificate for the physical diagonal versus the
q-Racah birth/death diagonal. The exceptional zero-spin endpoint is separate. -/
theorem casimir_diagonal_rational (q I M N X T : ℝ)
    (hq : q≠0) (hI : I≠0) (hM : M≠0) (hN : N≠0) (hX : X≠0) (hT : T≠0)
    (hD : q^2-1≠0) (h0 : I^2-1≠0) (h1 : I^2*q^2-1≠0) (h2 : I^2*q^4-1≠0) :
    (q-q⁻¹)^2*(symmetricQNumber q (M*q/X)*symmetricQNumber q X*N/T^2+
      X^2/M*symmetricQNumber q (N*q/T)*symmetricQNumber q T)+
      q*M*N/(X^2*T^2)+X^2*T^2/(q*M*N)-
      (q-q⁻¹)^2/I*(symmetricQNumber q (N*q/T)*symmetricQNumber q (X*q)*
        symmetricQNumber q T*symmetricQNumber q (M/X))/symmetricQNumber q I+
      (q-q⁻¹)^2/(I*q^2)*(symmetricQNumber q X*symmetricQNumber q (N/T)*
        symmetricQNumber q (T*q)*symmetricQNumber q (M*q/X))/symmetricQNumber q (I*q^2)=
    q*M*N+(q*M*N)⁻¹-
      (q-q⁻¹)^2*symmetricQNumber q (M/X)*symmetricQNumber q T*
        symmetricQNumber q (I*N*q/T)*symmetricQNumber q (I*X*q)/
          (symmetricQNumber q I*symmetricQNumber q (I*q))-
      (q-q⁻¹)^2*symmetricQNumber q X*symmetricQNumber q (N/T)*
        symmetricQNumber q (I*X*q/M)*symmetricQNumber q (I*q/T)/
          (symmetricQNumber q (I*q)*symmetricQNumber q (I*q^2)) := by
  have h1' : q^2*I^2-1≠0 := by convert h1 using 1 <;> ring
  have h2' : q^4*I^2-1≠0 := by convert h2 using 1 <;> ring
  unfold symmetricQNumber
  field_simp [hq,hI,hM,hN,hX,hT,hD,h0,h1,h2,h1',h2'] <;> ring

end AMSPhysical

#print axioms AMSPhysical.casimir_diagonal_rational

import QuantumJacobiStep
import QuantumNormNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def quantumLeftPathNorm (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  quantumHighestNorm q l m p.1*quantumHighestNorm q (coupledLabel l m p.1) n p.2

theorem quantumLeftPathNorm_pos (q : ℝ) (hq : 0<q) (l m n : ℕ) (p : LeftHighestPath l m n) :
    0<quantumLeftPathNorm q l m n p :=
  mul_pos (quantumHighestNorm_pos q hq _ _ _) (quantumHighestNorm_pos q hq _ _ _)

theorem projectedLeftLeading_sq (q : ℝ) (hq : 0<q) (l m n : ℕ) (p : LeftHighestPath l m n) :
    (projectedLeftLeading q l m n p)^2=(quantumLeftPathNorm q l m n p)⁻¹ := by
  unfold projectedLeftLeading quantumLeftPathNorm
  rw [mul_pow,inv_pow,inv_pow,Real.sq_sqrt (quantumHighestNorm_pos q hq _ _ _).le,
    Real.sq_sqrt (quantumHighestNorm_pos q hq _ _ _).le,mul_inv_rev]

theorem quantumRacahJacobi_step_sq_normalization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    (quantumRacahJacobi q hq hq1 l m n H p v)^2=
      (casimirLowerStep q m n p.val.1.val p.val.2.val)^2*
        quantumLeftPathNorm q l m n v.val/quantumLeftPathNorm q l m n p.val := by
  rw [quantumRacahJacobi_step q hq hq1 l m n H p v hnext,div_pow,mul_pow,
    projectedLeftLeading_sq q hq,projectedLeftLeading_sq q hq]
  simp only [div_eq_mul_inv,inv_inv]
  ring

/-- Exact cancellation of normalization factors and deformation phases. -/
theorem jacobi_norm_square_cancel (L H H0 G G0 P Q D R S U W I J K : ℝ)
    (hH : H≠0) (hG : G≠0) (hP : P≠0) (hR : R≠0) (hS : S≠0)
    (hI : I≠0) (hJ : J≠0) (hK : K≠0)
    (houter : H*U=P*R*J*K*H0) (hroot : G0*(S*I*J)=Q*W*G)
    (hphase : L^2*Q=D*R^2*S^2*P) :
    L^2*(H0*G0)/(H*G)=D*R*S*U*W/(I*J^2*K) := by
  have hH0 : H0=H*U/(P*R*J*K) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hP hR) hJ) hK)).mpr
    simpa only [mul_comm] using houter.symm
  have hG0 : G0=Q*W*G/(S*I*J) := (eq_div_iff (mul_ne_zero (mul_ne_zero hS hI) hJ)).mpr hroot
  rw [hH0,hG0]
  calc
    _=(L^2*Q)*U*W/(P*R*S*I*J^2*K) := by field_simp [hH,hG,hP,hR,hS,hI,hJ,hK]
    _=_ := by rw [hphase];field_simp [hP,hR,hS,hI,hJ,hK]

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_step_sq_normalization
#print axioms AMSPhysical.jacobi_norm_square_cancel

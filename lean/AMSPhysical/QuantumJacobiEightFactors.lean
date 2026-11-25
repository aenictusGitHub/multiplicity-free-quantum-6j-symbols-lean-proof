import QuantumPathNormNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def casimirJacobiNeighborSquare (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  (q-q⁻¹)^4*qnum q p.1.val*qnum q (n-p.2.val)*
    qnum q (l-p.1.val+1)*qnum q (m-p.1.val+1)*qnum q (l+m-p.1.val+2)*
    qnum q (p.2.val+1)*qnum q (coupledLabel l m p.1-p.2.val+1)*
    qnum q (coupledLabel l m p.1+n-p.2.val+2)/
      (qnum q (coupledLabel l m p.1+1)*(qnum q (coupledLabel l m p.1+2))^2*qnum q (coupledLabel l m p.1+3))

/-- Eight-factor formula for the squared neighboring entry of the actual physical Casimir. -/
theorem quantumRacahJacobi_step_sq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    (quantumRacahJacobi q hq hq1 l m n H p v)^2=casimirJacobiNeighborSquare q l m n p.val := by
  have hsecond := fixedLeftHighest_previous_second l m n H p v hnext
  have hn := channel_right_bound (coupledLabel l m v.val.1) n v.val.2
  have hs : p.val.2.val<n := by omega
  have hr : 0<p.val.1.val := by omega
  have houter := quantumHighestNorm_outer_neighbor q hq hq1 l m p.val.1 v.val.1 hnext
  have hroot := quantumHighestNorm_root_neighbor q hq hq1 l m n H p v hnext
  have hc := jacobi_norm_square_cancel
    (casimirLowerStep q m n p.val.1.val p.val.2.val)
    (quantumHighestNorm q l m p.val.1) (quantumHighestNorm q l m v.val.1)
    (quantumHighestNorm q (coupledLabel l m p.val.1) n p.val.2)
    (quantumHighestNorm q (coupledLabel l m v.val.1) n v.val.2)
    (q^(4*(p.val.1.val:ℤ)-2*(m:ℤ)-2)) (q^(4*(p.val.2.val:ℤ)+2-2*(n:ℤ))) ((q-q⁻¹)^4)
    (qnum q p.val.1.val) (qnum q (n-p.val.2.val))
    (qnum q (l-p.val.1.val+1)*qnum q (m-p.val.1.val+1)*qnum q (l+m-p.val.1.val+2))
    (qnum q (p.val.2.val+1)*qnum q (coupledLabel l m p.val.1-p.val.2.val+1)*
      qnum q (coupledLabel l m p.val.1+n-p.val.2.val+2))
    (qnum q (coupledLabel l m p.val.1+1)) (qnum q (coupledLabel l m p.val.1+2))
    (qnum q (coupledLabel l m p.val.1+3))
    (ne_of_gt (quantumHighestNorm_pos q hq _ _ _)) (ne_of_gt (quantumHighestNorm_pos q hq _ _ _))
    (zpow_ne_zero _ (ne_of_gt hq)) (ne_of_gt (qnum_pos q hq _ hr))
    (ne_of_gt (qnum_pos q hq _ (by omega)))
    (ne_of_gt (qnum_pos q hq _ (by omega))) (ne_of_gt (qnum_pos q hq _ (by omega)))
    (ne_of_gt (qnum_pos q hq _ (by omega))) houter
    (by simpa only [mul_assoc] using hroot)
    (casimirLowerStep_phase_square q hq hq1 m n _ _ hs.le)
  rw [quantumRacahJacobi_step_sq_normalization q hq hq1 l m n H p v hnext]
  unfold quantumLeftPathNorm
  rw [hc]
  unfold casimirJacobiNeighborSquare
  ring

/-- The positive sign is fixed by the independently proved coupling gauge. -/
theorem quantumRacahJacobi_step_sqrt (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p v=Real.sqrt (casimirJacobiNeighborSquare q l m n p.val) := by
  rw [← quantumRacahJacobi_step_sq q hq hq1 l m n H p v hnext,Real.sqrt_sq_eq_abs,
    abs_of_pos (quantumRacahJacobi_step_pos q hq hq1 l m n H p v hnext)]

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_step_sq
#print axioms AMSPhysical.quantumRacahJacobi_step_sqrt

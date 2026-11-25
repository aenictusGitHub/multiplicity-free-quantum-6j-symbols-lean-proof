import QuantumRacahJacobi

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module

def projectedLeftLeading (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) n p.2))⁻¹*
    (Real.sqrt (quantumHighestNorm q l m p.1))⁻¹

def casimirLowerStep (q : ℝ) (m n r s : ℕ) : ℝ :=
  (q-q⁻¹)^2*q^(-(m:ℤ)+2*((r:ℤ)-1))*qInteger q ((n:ℤ)-(s:ℤ))*
    qInteger q (r:ℤ)*q^((n:ℤ)-2*(s:ℤ))

theorem projectedLeftLeading_pos (q : ℝ) (hq : 0<q) (l m n : ℕ) (p : LeftHighestPath l m n) :
    0<projectedLeftLeading q l m n p :=
  mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))

theorem casimirLowerStep_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (m n r s : ℕ)
    (hr : 0<r) (hs : s<n) : 0<casimirLowerStep q m n r s := by
  unfold casimirLowerStep
  exact mul_pos (mul_pos (mul_pos (mul_pos
    (sq_pos_of_ne_zero (qInteger_denominator_ne_zero q hq hq1)) (zpow_pos hq _))
    (qInteger_pos_real q hq hq1 _ (by omega)))
    (qInteger_pos_real q hq hq1 _ (by omega))) (zpow_pos hq _)

theorem quantumLeftTreeHighest_Casimir_first_step (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    finiteTensorCoefficient m n ((p.1.val:ℤ)-1) ((p.2.val:ℤ)+1) (firstTripleProjection l m n
      (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)))=
      casimirLowerStep q m n p.1.val p.2.val*projectedLeftLeading q l m n p := by
  rw [firstTripleProjection_Casimir,finiteTensor_Casimir_coefficient q hq hq1 m n]
  rw [quantumLeftTreeHighest_projected_below q hq hq1 l m n p _ _ (by omega),
    quantumLeftTreeHighest_projected_below q hq hq1 l m n p _ _ (by omega)]
  have hy : (p.1.val:ℤ)-1+1=(p.1.val:ℤ) := by omega
  have hz : (p.2.val:ℤ)+1-1=(p.2.val:ℤ) := by omega
  rw [hy,hz,quantumLeftTreeHighest_projected_leading]
  have hn : (n:ℤ)-((p.2.val:ℤ)+1)+1=(n:ℤ)-(p.2.val:ℤ) := by omega
  rw [hn]
  unfold casimirLowerStep projectedLeftLeading
  ring

/-- The neighboring Jacobi entry is fixed by the first nonzero projected coordinate. -/
theorem quantumRacahJacobi_step (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p v=
      casimirLowerStep q m n p.val.1.val p.val.2.val*
        projectedLeftLeading q l m n p.val/projectedLeftLeading q l m n v.val := by
  classical
  have he := triangular_expansion_leading
    (V:=RealQuantumTripleSpace l m n)
    (fun a : FixedLeftHighest l m n H => quantumLeftTreeHighest q hq hq1 l m n a.val.1 a.val.2)
    (fun a => a.val.1.val) (fixedLeftHighest_index_injective l m n H)
    (fixedHighestCoordinate l m n H) (fixedHighestCoordinate_triangular q hq hq1 l m n H)
    (quantumRacahJacobi q hq hq1 l m n H p)
    (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2))
    (quantumRacahJacobi_expansion q hq hq1 l m n H p) v
    (fun a ha => quantumRacahJacobi_hessenberg q hq hq1 l m n H p a
      (by change a.val.1.val<v.val.1.val at ha;omega))
  have hdefp := fixedLeftHighest_defect l m n H p
  have hdefv := fixedLeftHighest_defect l m n H v
  have hyr : (v.val.1.val:ℤ)=(p.val.1.val:ℤ)-1 := by omega
  have hzr : (leftHighestDefect l m n H:ℤ)-(v.val.1.val:ℤ)=(p.val.2.val:ℤ)+1 := by omega
  have hdiag : fixedHighestCoordinate l m n H v.val.1.val
      (quantumLeftTreeHighest q hq hq1 l m n v.val.1 v.val.2)=projectedLeftLeading q l m n v.val := by
    unfold fixedHighestCoordinate
    rw [LinearMap.comp_apply,show (leftHighestDefect l m n H:ℤ)-(v.val.1.val:ℤ)=(v.val.2.val:ℤ) by omega,
      quantumLeftTreeHighest_projected_leading]
    rfl
  rw [hdiag] at he
  unfold fixedHighestCoordinate at he
  rw [LinearMap.comp_apply,hzr,hyr,quantumLeftTreeHighest_Casimir_first_step] at he
  exact (eq_div_iff (ne_of_gt (projectedLeftLeading_pos q hq l m n v.val))).mpr he.symm

theorem quantumRacahJacobi_step_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    0<quantumRacahJacobi q hq hq1 l m n H p v := by
  rw [quantumRacahJacobi_step q hq hq1 l m n H p v hnext]
  have hp := fixedLeftHighest_defect l m n H p
  have hv := fixedLeftHighest_defect l m n H v
  have hbound := channel_right_bound (coupledLabel l m v.val.1) n v.val.2
  apply div_pos (mul_pos (casimirLowerStep_pos q hq hq1 m n _ _ (by omega) (by omega))
    (projectedLeftLeading_pos q hq l m n p.val)) (projectedLeftLeading_pos q hq l m n v.val)

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_step
#print axioms AMSPhysical.quantumRacahJacobi_step_pos

import QuantumProjectedNext
import QuantumChannelNeighbors
import TriangularNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open Module

def casimirDiagonalWeight (q : ℝ) (m n r s : ℕ) : ℝ :=
  (q-q⁻¹)^2*(qInteger q ((m:ℤ)-(r:ℤ)+1)*qInteger q (r:ℤ)*q^((n:ℤ)-2*(s:ℤ))+
    q^(-(m:ℤ)+2*(r:ℤ))*qInteger q ((n:ℤ)-(s:ℤ)+1)*qInteger q (s:ℤ))+
    q*q^((m:ℤ)+(n:ℤ)-2*((r:ℤ)+(s:ℤ)))+
    q⁻¹*q^(-((m:ℤ)+(n:ℤ)-2*((r:ℤ)+(s:ℤ))))

def casimirUpperInputStep (q : ℝ) (m n r s : ℕ) : ℝ :=
  (q-q⁻¹)^2*q^(-(m:ℤ)+2*(r:ℤ))*qInteger q ((n:ℤ)-(s:ℤ)+1)*
    qInteger q ((r:ℤ)+1)*q^((n:ℤ)-2*((s:ℤ)-1))

def previousProjectedNextRatio (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  -q^(-(l:ℤ)-(n:ℤ)+2*(p.2.val:ℤ))*qInteger q ((p.2.val:ℤ)+1)*
    qInteger q ((m:ℤ)-(p.1.val:ℤ)+1)/qInteger q ((coupledLabel l m p.1:ℤ)+2)

def casimirJacobiDiagonalClosed (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  casimirDiagonalWeight q m n p.1.val p.2.val+
    casimirUpperInputStep q m n p.1.val p.2.val*projectedLeftNextRatio q l m n p-
      casimirLowerStep q m n p.1.val p.2.val*previousProjectedNextRatio q l m n p

theorem quantumLeftTreeHighest_Casimir_diagonal_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    finiteTensorCoefficient m n p.1.val p.2.val (firstTripleProjection l m n
      (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)))=
      projectedLeftLeading q l m n p*(casimirDiagonalWeight q m n p.1.val p.2.val+
        casimirUpperInputStep q m n p.1.val p.2.val*projectedLeftNextRatio q l m n p) := by
  rw [firstTripleProjection_Casimir,finiteTensor_Casimir_coefficient q hq hq1 m n]
  rw [quantumLeftTreeHighest_projected_below q hq hq1 l m n p
    ((p.1.val:ℤ)-1) ((p.2.val:ℤ)+1) (by omega),quantumLeftTreeHighest_projected_leading,
    quantumLeftTreeHighest_projected_next]
  unfold casimirDiagonalWeight casimirUpperInputStep projectedLeftLeading
  ring

theorem previousProjectedNextRatio_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    projectedLeftNextRatio q l m n v.val=previousProjectedNextRatio q l m n p.val := by
  rw [projectedLeftNextRatio_closed q hq hq1]
  have hs := fixedLeftHighest_previous_second l m n H p v hnext
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hlabel : (coupledLabel l m v.val.1:ℤ)=(coupledLabel l m p.val.1:ℤ)+2 := by
    unfold coupledLabel
    omega
  have hphase : -(l:ℤ)-(n:ℤ)+2*(v.val.2.val:ℤ)-2=-(l:ℤ)-(n:ℤ)+2*(p.val.2.val:ℤ) := by omega
  have hmphase : (m:ℤ)-(v.val.1.val:ℤ)=(m:ℤ)-(p.val.1.val:ℤ)+1 := by omega
  have hsphase : (v.val.2.val:ℤ)=(p.val.2.val:ℤ)+1 := by omega
  rw [hlabel,hphase,hmphase,hsphase]
  rfl

theorem fixedHighestCoordinate_leading_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) :
    fixedHighestCoordinate l m n H p.val.1.val (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2)=
      projectedLeftLeading q l m n p.val := by
  unfold fixedHighestCoordinate
  have hp := fixedLeftHighest_defect l m n H p
  rw [LinearMap.comp_apply,show (leftHighestDefect l m n H:ℤ)-(p.val.1.val:ℤ)=(p.val.2.val:ℤ) by omega,
    quantumLeftTreeHighest_projected_leading]
  rfl

theorem fixedHighestCoordinate_next_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    fixedHighestCoordinate l m n H p.val.1.val (quantumLeftTreeHighest q hq hq1 l m n v.val.1 v.val.2)=
      projectedLeftLeading q l m n v.val*projectedLeftNextRatio q l m n v.val := by
  unfold fixedHighestCoordinate
  rw [LinearMap.comp_apply]
  have hv := fixedLeftHighest_defect l m n H v
  have hy : (p.val.1.val:ℤ)=(v.val.1.val:ℤ)+1 := by omega
  have hz : (leftHighestDefect l m n H:ℤ)-(p.val.1.val:ℤ)=(v.val.2.val:ℤ)-1 := by omega
  rw [hz,hy]
  exact quantumLeftTreeHighest_projected_next q hq hq1 l m n v.val

theorem fixedHighestCoordinate_Casimir_diagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) :
    fixedHighestCoordinate l m n H p.val.1.val
      (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2))=
      projectedLeftLeading q l m n p.val*(casimirDiagonalWeight q m n p.val.1.val p.val.2.val+
        casimirUpperInputStep q m n p.val.1.val p.val.2.val*projectedLeftNextRatio q l m n p.val) := by
  unfold fixedHighestCoordinate
  rw [LinearMap.comp_apply]
  have hp := fixedLeftHighest_defect l m n H p
  rw [show (leftHighestDefect l m n H:ℤ)-(p.val.1.val:ℤ)=(p.val.2.val:ℤ) by omega]
  exact quantumLeftTreeHighest_Casimir_diagonal_coordinate q hq hq1 l m n p.val

theorem quantumRacahJacobi_diagonal_interior (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p p=casimirJacobiDiagonalClosed q l m n p.val := by
  classical
  have he := triangular_expansion_two (V:=RealQuantumTripleSpace l m n)
    (fun a : FixedLeftHighest l m n H => quantumLeftTreeHighest q hq hq1 l m n a.val.1 a.val.2)
    (fun a => a.val.1.val) (fixedLeftHighest_index_injective l m n H)
    (fixedHighestCoordinate l m n H) (fixedHighestCoordinate_triangular q hq hq1 l m n H)
    (quantumRacahJacobi q hq hq1 l m n H p)
    (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2))
    (quantumRacahJacobi_expansion q hq hq1 l m n H p) p v hnext
    (fun a ha => quantumRacahJacobi_hessenberg q hq hq1 l m n H p a ha)
  change fixedHighestCoordinate l m n H p.val.1.val _=
    quantumRacahJacobi q hq hq1 l m n H p p*fixedHighestCoordinate l m n H p.val.1.val _+
      quantumRacahJacobi q hq hq1 l m n H p v*fixedHighestCoordinate l m n H p.val.1.val _ at he
  rw [fixedHighestCoordinate_Casimir_diagonal q hq hq1 l m n H p,
    fixedHighestCoordinate_leading_eq q hq hq1 l m n H p,
    fixedHighestCoordinate_next_eq q hq hq1 l m n H p v hnext,
    previousProjectedNextRatio_eq q hq hq1 l m n H p v hnext] at he
  have hstep := (eq_div_iff (ne_of_gt (projectedLeftLeading_pos q hq l m n v.val))).mp
    (quantumRacahJacobi_step q hq hq1 l m n H p v hnext)
  apply mul_right_cancel₀ (ne_of_gt (projectedLeftLeading_pos q hq l m n p.val))
  unfold casimirJacobiDiagonalClosed
  linear_combination -he-previousProjectedNextRatio q l m n p.val*hstep

theorem casimirLowerStep_boundary_zero (q : ℝ) (m n r s : ℕ) (hbound : r=0 ∨ s=n) :
    casimirLowerStep q m n r s=0 := by
  rcases hbound with hr | hs
  · simp only [casimirLowerStep,hr,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul]
  · simp only [casimirLowerStep,hs,sub_self,qInteger_zero,mul_zero,zero_mul]

theorem quantumRacahJacobi_diagonal_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (hbound : p.val.1.val=0 ∨ p.val.2.val=n) :
    quantumRacahJacobi q hq hq1 l m n H p p=casimirJacobiDiagonalClosed q l m n p.val := by
  classical
  have he := triangular_expansion_leading (V:=RealQuantumTripleSpace l m n)
    (fun a : FixedLeftHighest l m n H => quantumLeftTreeHighest q hq hq1 l m n a.val.1 a.val.2)
    (fun a => a.val.1.val) (fixedLeftHighest_index_injective l m n H)
    (fixedHighestCoordinate l m n H) (fixedHighestCoordinate_triangular q hq hq1 l m n H)
    (quantumRacahJacobi q hq hq1 l m n H p)
    (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2))
    (quantumRacahJacobi_expansion q hq hq1 l m n H p) p
    (fun a ha => False.elim (by
      have hh := fixedLeftHighest_boundary_minimal l m n H p hbound a
      change a.val.1.val<p.val.1.val at ha
      omega))
  change fixedHighestCoordinate l m n H p.val.1.val _=
    quantumRacahJacobi q hq hq1 l m n H p p*fixedHighestCoordinate l m n H p.val.1.val _ at he
  rw [fixedHighestCoordinate_Casimir_diagonal q hq hq1 l m n H p,
    fixedHighestCoordinate_leading_eq q hq hq1 l m n H p] at he
  unfold casimirJacobiDiagonalClosed
  rw [casimirLowerStep_boundary_zero q m n _ _ hbound,zero_mul,sub_zero]
  apply mul_right_cancel₀ (ne_of_gt (projectedLeftLeading_pos q hq l m n p.val))
  linear_combination -he

/-- Closed diagonal of the physical Casimir recurrence, including boundary channels. -/
theorem quantumRacahJacobi_diagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) :
    quantumRacahJacobi q hq hq1 l m n H p p=casimirJacobiDiagonalClosed q l m n p.val := by
  by_cases hr : p.val.1.val=0
  · exact quantumRacahJacobi_diagonal_boundary q hq hq1 l m n H p (Or.inl hr)
  by_cases hs : p.val.2.val=n
  · exact quantumRacahJacobi_diagonal_boundary q hq hq1 l m n H p (Or.inr hs)
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  obtain ⟨v,hv⟩ := fixedLeftHighest_previous l m n H p (by omega) (by omega)
  exact quantumRacahJacobi_diagonal_interior q hq hq1 l m n H p v hv

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_diagonal

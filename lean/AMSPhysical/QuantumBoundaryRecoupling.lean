import QuantumJacobiDiagonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module

def rightTotalLabel (l m n : ℕ) (a : RightHighestPath l m n) : ℕ :=
  coupledLabel l (coupledLabel m n a.1) a.2

theorem rightTotalLabel_defect (l m n : ℕ) (a : RightHighestPath l m n) :
    l+m+n=rightTotalLabel l m n a+2*(a.1.val+a.2.val) := by
  have hm := channel_left_bound m n a.1
  have hn := channel_right_bound m n a.1
  have hl := channel_left_bound l (coupledLabel m n a.1) a.2
  have hj := channel_right_bound l (coupledLabel m n a.1) a.2
  unfold rightTotalLabel coupledLabel at *
  omega

/-- An extremal projected coordinate fixes the actual physical normalization. -/
theorem quantumRacah_boundary_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (hbound : p.val.1.val=0 ∨ p.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    quantumRacahMatrix q hq hq1 l m n p.val a*projectedLeftLeading q l m n p.val=
      (Real.sqrt (quantumHighestNorm q l (coupledLabel m n a.1) a.2))⁻¹*
        standardClebschCoefficient q hq hq1 m n a.1 (rightPathWeightIndex l m n a) p.val.1.val p.val.2.val := by
  classical
  have hK := quantumRightTreeHighest_K q hq hq1 l m n a
  change _=q^(rightTotalLabel l m n a:ℤ) • _ at hK
  rw [hH] at hK
  have he := triangular_expansion_leading (V:=RealQuantumTripleSpace l m n)
    (fun b : FixedLeftHighest l m n H => quantumLeftTreeHighest q hq hq1 l m n b.val.1 b.val.2)
    (fun b => b.val.1.val) (fixedLeftHighest_index_injective l m n H)
    (fixedHighestCoordinate l m n H) (fixedHighestCoordinate_triangular q hq hq1 l m n H)
    (fun b => quantumTripleBilin q l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)
      (quantumLeftTreeHighest q hq hq1 l m n b.val.1 b.val.2))
    (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)
    (quantumHighest_fixed_left_expansion q hq hq1 l m n H _ (quantumRightTreeHighest_E q hq hq1 l m n a) hK) p
    (fun b hb => False.elim (by
      have hh := fixedLeftHighest_boundary_minimal l m n H p hbound b
      change b.val.1.val<p.val.1.val at hb
      omega))
  change fixedHighestCoordinate l m n H p.val.1.val _=
    quantumTripleBilin q l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)
      (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2)*
      fixedHighestCoordinate l m n H p.val.1.val _ at he
  rw [fixedHighestCoordinate_leading_eq q hq hq1 l m n H p,
    quantumTripleBilin_symm q hq hq1 l m n (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)
      (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2)] at he
  have hp := fixedLeftHighest_defect l m n H p
  unfold fixedHighestCoordinate at he
  rw [LinearMap.comp_apply,show (leftHighestDefect l m n H:ℤ)-(p.val.1.val:ℤ)=(p.val.2.val:ℤ) by omega,
    firstTripleProjection_rightHighest,map_smul,smul_eq_mul] at he
  exact he.symm

end AMSPhysical

#print axioms AMSPhysical.quantumRacah_boundary_projection

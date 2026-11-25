import QuantumFixedHighest
import QuantumCasimirCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module

/-- The intermediate Casimir in the actual orthonormal left channel basis. -/
def quantumRacahJacobi (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ) :
    Matrix (FixedLeftHighest l m n H) (FixedLeftHighest l m n H) ℝ :=
  fun p v => quantumTripleBilin q l m n
    (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2))
    (quantumLeftTreeHighest q hq hq1 l m n v.val.1 v.val.2)

theorem quantumRacahJacobi_symmetric (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) :
    quantumRacahJacobi q hq hq1 l m n H p v=quantumRacahJacobi q hq hq1 l m n H v p := by
  unfold quantumRacahJacobi
  rw [rightIntermediateCasimir_adjoint q hq hq1 l m n _ _]
  exact quantumTripleBilin_symm q hq hq1 l m n _ _

theorem quantumRacahJacobi_expansion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) :
    (∑ v : FixedLeftHighest l m n H,quantumRacahJacobi q hq hq1 l m n H p v •
      quantumLeftTreeHighest q hq hq1 l m n v.val.1 v.val.2)=
      rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2) := by
  apply quantumHighest_fixed_left_expansion q hq hq1 l m n H
  · rw [rightIntermediateCasimir_intertwines q hq hq1 l m n (uqGenerator q 0) _,
      quantumLeftTreeHighest_E q hq hq1 l m n p.val,map_zero]
  · rw [rightIntermediateCasimir_intertwines q hq hq1 l m n (uqGenerator q 2) _,
      quantumLeftTreeHighest_K q hq hq1 l m n p.val,map_smul]
    rw [show coupledLabel (coupledLabel l m p.val.1) n p.val.2=H from p.property]

theorem quantumRacahJacobi_hessenberg (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hfar : v.val.1.val+1<p.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p v=0 := by
  classical
  have hc := triangular_expansion_cutoff
    (V:=RealQuantumTripleSpace l m n)
    (fun a : FixedLeftHighest l m n H => quantumLeftTreeHighest q hq hq1 l m n a.val.1 a.val.2)
    (fun a => a.val.1.val) (fixedLeftHighest_index_injective l m n H)
    (fixedHighestCoordinate l m n H)
    (fixedHighestCoordinate_triangular q hq hq1 l m n H)
    (fun a => ne_of_gt (fixedHighestCoordinate_diagonal_pos q hq hq1 l m n H a))
    (quantumRacahJacobi q hq hq1 l m n H p)
    (rightIntermediateCasimir q hq hq1 l m n (quantumLeftTreeHighest q hq hq1 l m n p.val.1 p.val.2))
    (quantumRacahJacobi_expansion q hq hq1 l m n H p) (p.val.1.val-1)
    (fun y hy => quantumLeftTreeHighest_Casimir_projected_below q hq hq1 l m n p.val y
      ((leftHighestDefect l m n H:ℤ)-(y:ℤ)) (by omega))
  exact hc v (by change v.val.1.val<p.val.1.val-1;omega)

/-- A kernel-checked tridiagonal recurrence operator for the physical rank-two overlaps. -/
theorem quantumRacahJacobi_tridiagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H)
    (hfar : v.val.1.val+1<p.val.1.val ∨ p.val.1.val+1<v.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p v=0 := by
  exact symmetric_hessenberg_tridiagonal (quantumRacahJacobi q hq hq1 l m n H)
    (fun a => a.val.1.val) (quantumRacahJacobi_symmetric q hq hq1 l m n H)
    (quantumRacahJacobi_hessenberg q hq hq1 l m n H) p v hfar

/-- The independently constructed recoupling coefficients satisfy the actual Casimir recurrence. -/
theorem quantumRacah_Casimir_recurrence (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) :
    (∑ v : FixedLeftHighest l m n H,quantumRacahJacobi q hq hq1 l m n H p v*
      quantumRacahMatrix q hq hq1 l m n v.val a)=
      quantumCasimirEigen q (coupledLabel m n a.1)*quantumRacahMatrix q hq hq1 l m n p.val a := by
  have he := congrArg (fun w : RealQuantumTripleSpace l m n => quantumTripleBilin q l m n w
    (quantumRightTreeHighest q hq hq1 l m n a.1 a.2)) (quantumRacahJacobi_expansion q hq hq1 l m n H p)
  dsimp only at he
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul] at he
  change (∑ v : FixedLeftHighest l m n H,quantumRacahJacobi q hq hq1 l m n H p v*
      quantumRacahMatrix q hq hq1 l m n v.val a)=_ at he
  rw [he,rightIntermediateCasimir_adjoint q hq hq1 l m n _ _]
  change quantumTripleBilin q l m n _
    (rightIntermediateCasimir q hq hq1 l m n (quantumRightTreeMap q hq hq1 l m n a.1 a.2
      (standardWeightBasis (coupledLabel l (coupledLabel m n a.1) a.2) 0)))=_
  rw [rightIntermediateCasimir_tree,map_smul,smul_eq_mul]
  unfold quantumRacahMatrix quantumRacahEntry quantumRightTreeHighest
  ring

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_tridiagonal
#print axioms AMSPhysical.quantumRacah_Casimir_recurrence

import QuantumFusionBases
import OrthonormalBasisChange

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module

/-- Full normalized change of the two actual three-factor fusion bases, including weight indices. -/
def fullQuantumRecouplingMatrix (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    Matrix (LeftFusionIndex l m n) (RightFusionIndex l m n) ℝ :=
  fun i j => quantumTripleBilin q l m n (leftFusionVector q hq hq1 l m n i) (rightFusionVector q hq hq1 l m n j)

theorem fullQuantumRecoupling_rows (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (i j : LeftFusionIndex l m n) :
    (∑ k,fullQuantumRecouplingMatrix q hq hq1 l m n i k*fullQuantumRecouplingMatrix q hq hq1 l m n j k)=
      if i=j then 1 else 0 := by
  have hb (i j : LeftFusionIndex l m n) : quantumTripleBilin q l m n
      (quantumLeftFusionBasis q hq hq1 l m n i) (quantumLeftFusionBasis q hq hq1 l m n j)=if i=j then 1 else 0 := by
    rw [quantumLeftFusionBasis_apply,quantumLeftFusionBasis_apply]
    exact leftFusionVector_pair q hq hq1 l m n i j
  have hc (i j : RightFusionIndex l m n) : quantumTripleBilin q l m n
      (quantumRightFusionBasis q hq hq1 l m n i) (quantumRightFusionBasis q hq hq1 l m n j)=if i=j then 1 else 0 := by
    rw [quantumRightFusionBasis_apply,quantumRightFusionBasis_apply]
    exact rightFusionVector_pair q hq hq1 l m n i j
  have he := orthonormal_basis_change_rows (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
    (quantumLeftFusionBasis q hq hq1 l m n) (quantumRightFusionBasis q hq hq1 l m n) hb hc i j
  simpa only [quantumLeftFusionBasis_apply,quantumRightFusionBasis_apply,fullQuantumRecouplingMatrix] using he

theorem fullQuantumRecoupling_cols (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (i j : RightFusionIndex l m n) :
    (∑ k,fullQuantumRecouplingMatrix q hq hq1 l m n k i*fullQuantumRecouplingMatrix q hq hq1 l m n k j)=
      if i=j then 1 else 0 := by
  have hb (i j : LeftFusionIndex l m n) : quantumTripleBilin q l m n
      (quantumLeftFusionBasis q hq hq1 l m n i) (quantumLeftFusionBasis q hq hq1 l m n j)=if i=j then 1 else 0 := by
    rw [quantumLeftFusionBasis_apply,quantumLeftFusionBasis_apply]
    exact leftFusionVector_pair q hq hq1 l m n i j
  have hc (i j : RightFusionIndex l m n) : quantumTripleBilin q l m n
      (quantumRightFusionBasis q hq hq1 l m n i) (quantumRightFusionBasis q hq hq1 l m n j)=if i=j then 1 else 0 := by
    rw [quantumRightFusionBasis_apply,quantumRightFusionBasis_apply]
    exact rightFusionVector_pair q hq hq1 l m n i j
  have he := orthonormal_basis_change_cols (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
    (quantumLeftFusionBasis q hq hq1 l m n) (quantumRightFusionBasis q hq hq1 l m n) hb hc i j
  simpa only [quantumLeftFusionBasis_apply,quantumRightFusionBasis_apply,fullQuantumRecouplingMatrix] using he

theorem fullQuantumRecoupling_mul_transpose (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    fullQuantumRecouplingMatrix q hq hq1 l m n*(fullQuantumRecouplingMatrix q hq hq1 l m n).transpose=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
  exact fullQuantumRecoupling_rows q hq hq1 l m n i j

theorem fullQuantumRecoupling_transpose_mul (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    (fullQuantumRecouplingMatrix q hq hq1 l m n).transpose*fullQuantumRecouplingMatrix q hq hq1 l m n=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
  exact fullQuantumRecoupling_cols q hq hq1 l m n i j

end AMSPhysical

#print axioms AMSPhysical.fullQuantumRecoupling_mul_transpose
#print axioms AMSPhysical.fullQuantumRecoupling_transpose_mul

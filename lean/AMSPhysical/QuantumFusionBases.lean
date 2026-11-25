import QuantumOrthonormalBasis
import QuantumTreeOrthogonality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

abbrev LeftFusionIndex (l m n : ℕ) :=
  (r : Fin (min l m+1)) × CoupledIndex (coupledLabel l m r) n
abbrev RightFusionIndex (l m n : ℕ) :=
  (u : Fin (min m n+1)) × CoupledIndex l (coupledLabel m n u)

def leftFusionVector (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : LeftFusionIndex l m n) :
    RealQuantumTripleSpace l m n :=
  quantumLeftTreeMap q hq hq1 l m n p.1 p.2.1
    (orthonormalWeightVector q (coupledLabel (coupledLabel l m p.1) n p.2.1) p.2.2)

def rightFusionVector (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : RightFusionIndex l m n) :
    RealQuantumTripleSpace l m n :=
  quantumRightTreeMap q hq hq1 l m n p.1 p.2.1
    (orthonormalWeightVector q (coupledLabel l (coupledLabel m n p.1) p.2.1) p.2.2)

theorem leftFusionVector_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p v : LeftFusionIndex l m n) :
    quantumTripleBilin q l m n (leftFusionVector q hq hq1 l m n p)
      (leftFusionVector q hq hq1 l m n v)=if p=v then 1 else 0 := by
  classical
  have hself (r : Fin (min l m+1)) (a b : CoupledIndex (coupledLabel l m r) n) :
      quantumTripleBilin q l m n (leftFusionVector q hq hq1 l m n ⟨r,a⟩)
        (leftFusionVector q hq hq1 l m n ⟨r,b⟩)=if a=b then 1 else 0 := by
    apply sigmaOrthonormal_pair (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
      (fun s k => quantumLeftTreeMap q hq hq1 l m n r s
        (orthonormalWeightVector q (coupledLabel (coupledLabel l m r) n s) k))
    · intro s i j
      rw [quantumLeftTreeMap_isometry,orthonormalWeightVector_pair q hq]
    · intro s s' hss i j
      exact quantumLeftTreeMap_inner_orthogonal q hq hq1 l m n r s s' hss _ _
  apply sigmaOrthonormal_pair (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
    (fun r a => leftFusionVector q hq hq1 l m n ⟨r,a⟩) hself
  intro r r' hrr a b
  exact quantumLeftTreeMap_outer_orthogonal q hq hq1 l m n r r' hrr a.1 b.1 _ _

theorem rightFusionVector_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p v : RightFusionIndex l m n) :
    quantumTripleBilin q l m n (rightFusionVector q hq hq1 l m n p)
      (rightFusionVector q hq hq1 l m n v)=if p=v then 1 else 0 := by
  classical
  have hself (u : Fin (min m n+1)) (a b : CoupledIndex l (coupledLabel m n u)) :
      quantumTripleBilin q l m n (rightFusionVector q hq hq1 l m n ⟨u,a⟩)
        (rightFusionVector q hq hq1 l m n ⟨u,b⟩)=if a=b then 1 else 0 := by
    apply sigmaOrthonormal_pair (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
      (fun v k => quantumRightTreeMap q hq hq1 l m n u v
        (orthonormalWeightVector q (coupledLabel l (coupledLabel m n u) v) k))
    · intro v i j
      rw [quantumRightTreeMap_isometry,orthonormalWeightVector_pair q hq]
    · intro v v' hvv i j
      exact quantumRightTreeMap_inner_orthogonal q hq hq1 l m n u v v' hvv _ _
  apply sigmaOrthonormal_pair (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
    (fun u a => rightFusionVector q hq hq1 l m n ⟨u,a⟩) hself
  intro u u' huu a b
  exact quantumRightTreeMap_outer_orthogonal q hq hq1 l m n u u' huu a.1 b.1 _ _

theorem leftFusionIndex_card (l m n : ℕ) :
    Fintype.card (LeftFusionIndex l m n)=(l+1)*(m+1)*(n+1) := by
  rw [Fintype.card_sigma]
  simp only [coupledIndex_card]
  rw [← Finset.sum_mul]
  have hsum : (∑ r : Fin (min l m+1),(coupledLabel l m r+1))=(l+1)*(m+1) := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using coupledIndex_card l m
  rw [hsum]

theorem rightFusionIndex_card (l m n : ℕ) :
    Fintype.card (RightFusionIndex l m n)=(l+1)*(m+1)*(n+1) := by
  rw [Fintype.card_sigma]
  simp only [coupledIndex_card]
  rw [← Finset.mul_sum]
  have hsum : (∑ u : Fin (min m n+1),(coupledLabel m n u+1))=(m+1)*(n+1) := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using coupledIndex_card m n
  rw [hsum,mul_assoc]

def quantumLeftFusionBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    Basis (LeftFusionIndex l m n) ℝ (RealQuantumTripleSpace l m n) := by
  letI : Nonempty (LeftFusionIndex l m n) := ⟨⟨0,0,0⟩⟩
  have hi := bilinear_orthonormal_independent (V:=RealQuantumTripleSpace l m n)
    (quantumTripleBilin q l m n) (leftFusionVector q hq hq1 l m n) (leftFusionVector_pair q hq hq1 l m n)
  exact basisOfLinearIndependentOfCardEqFinrank (K:=ℝ) (V:=RealQuantumTripleSpace l m n) hi (by
    rw [leftFusionIndex_card,Module.finrank_tensorProduct,Module.finrank_tensorProduct,
      finiteWeightSpace_finrank,finiteWeightSpace_finrank,finiteWeightSpace_finrank])

def quantumRightFusionBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    Basis (RightFusionIndex l m n) ℝ (RealQuantumTripleSpace l m n) := by
  letI : Nonempty (RightFusionIndex l m n) := ⟨⟨0,0,0⟩⟩
  have hi := bilinear_orthonormal_independent (V:=RealQuantumTripleSpace l m n)
    (quantumTripleBilin q l m n) (rightFusionVector q hq hq1 l m n) (rightFusionVector_pair q hq hq1 l m n)
  exact basisOfLinearIndependentOfCardEqFinrank (K:=ℝ) (V:=RealQuantumTripleSpace l m n) hi (by
    rw [rightFusionIndex_card,Module.finrank_tensorProduct,Module.finrank_tensorProduct,
      finiteWeightSpace_finrank,finiteWeightSpace_finrank,finiteWeightSpace_finrank])

theorem quantumLeftFusionBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftFusionIndex l m n) : quantumLeftFusionBasis q hq hq1 l m n p=leftFusionVector q hq hq1 l m n p := by
  simp [quantumLeftFusionBasis]

theorem quantumRightFusionBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : RightFusionIndex l m n) : quantumRightFusionBasis q hq hq1 l m n p=rightFusionVector q hq hq1 l m n p := by
  simp [quantumRightFusionBasis]

end AMSPhysical

#print axioms AMSPhysical.quantumLeftFusionBasis
#print axioms AMSPhysical.quantumRightFusionBasis

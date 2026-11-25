import QuantumFusionRecoupling
import QuantumTreeIntertwiner
import QuantumHighestOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module

abbrev LeftHighestPath (l m n : ℕ) :=
  (r : Fin (min l m+1)) × Fin (min (coupledLabel l m r) n+1)
abbrev RightHighestPath (l m n : ℕ) :=
  (u : Fin (min m n+1)) × Fin (min l (coupledLabel m n u)+1)

def leftHighestEmbedding (l m n : ℕ) (p : LeftHighestPath l m n) : LeftFusionIndex l m n :=
  ⟨p.1,⟨p.2,0⟩⟩
def rightHighestEmbedding (l m n : ℕ) (p : RightHighestPath l m n) : RightFusionIndex l m n :=
  ⟨p.1,⟨p.2,0⟩⟩

theorem leftHighestEmbedding_injective (l m n : ℕ) : Function.Injective (leftHighestEmbedding l m n) := by
  have h : Function.LeftInverse (fun p : LeftFusionIndex l m n => (⟨p.1,p.2.1⟩ : LeftHighestPath l m n))
      (leftHighestEmbedding l m n) := fun _ => rfl
  exact h.injective

theorem rightHighestEmbedding_injective (l m n : ℕ) : Function.Injective (rightHighestEmbedding l m n) := by
  have h : Function.LeftInverse (fun p : RightFusionIndex l m n => (⟨p.1,p.2.1⟩ : RightHighestPath l m n))
      (rightHighestEmbedding l m n) := fun _ => rfl
  exact h.injective

theorem orthonormalWeightVector_zero (q : ℝ) (hq : 0<q) (L : ℕ) :
    orthonormalWeightVector q L 0=standardWeightBasis L 0 := by
  unfold orthonormalWeightVector
  change (Real.sqrt (quantumWeight q L 0))⁻¹ • standardWeightBasis L 0=standardWeightBasis L 0
  rw [quantumWeight_zero q hq,Real.sqrt_one,inv_one,one_smul]

theorem leftFusionHighest_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : LeftHighestPath l m n) :
    leftFusionVector q hq hq1 l m n (leftHighestEmbedding l m n p)=quantumLeftTreeHighest q hq hq1 l m n p.1 p.2 := by
  unfold leftFusionVector leftHighestEmbedding quantumLeftTreeHighest
  rw [orthonormalWeightVector_zero q hq]

theorem rightFusionHighest_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : RightHighestPath l m n) :
    rightFusionVector q hq hq1 l m n (rightHighestEmbedding l m n p)=quantumRightTreeHighest q hq hq1 l m n p.1 p.2 := by
  unfold rightFusionVector rightHighestEmbedding quantumRightTreeHighest
  rw [orthonormalWeightVector_zero q hq]

theorem quantumTripleBilin_symm (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p v : RealQuantumTripleSpace l m n) : quantumTripleBilin q l m n p v=quantumTripleBilin q l m n v p := by
  apply orthonormal_basis_symm (V:=RealQuantumTripleSpace l m n) (quantumTripleBilin q l m n)
    (quantumLeftFusionBasis q hq hq1 l m n)
  intro i j
  rw [quantumLeftFusionBasis_apply,quantumLeftFusionBasis_apply]
  exact leftFusionVector_pair q hq hq1 l m n i j

theorem quantumLeftTreeHighest_E (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : LeftHighestPath l m n) :
    finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 0)
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)=0 :=
  quantumIntertwiner_highest_E (W:=RealQuantumTripleSpace l m n) q hq hq1
    (coupledLabel (coupledLabel l m p.1) n p.2) _ _ (quantumLeftTreeMap_intertwines q hq hq1 l m n p.1 p.2)

theorem quantumRightTreeHighest_E (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : RightHighestPath l m n) :
    finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 0)
      (quantumRightTreeHighest q hq hq1 l m n p.1 p.2)=0 :=
  quantumIntertwiner_highest_E (W:=RealQuantumTripleSpace l m n) q hq hq1
    (coupledLabel l (coupledLabel m n p.1) p.2) _ _ (quantumRightTreeMap_intertwines q hq hq1 l m n p.1 p.2)

theorem quantumLeftTreeHighest_K (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : LeftHighestPath l m n) :
    finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 2)
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)=
      q^(coupledLabel (coupledLabel l m p.1) n p.2:ℤ) • quantumLeftTreeHighest q hq hq1 l m n p.1 p.2 := by
  have h := quantumIntertwiner_K_basis (W:=RealQuantumTripleSpace l m n) q hq hq1
    (coupledLabel (coupledLabel l m p.1) n p.2) _ _ (quantumLeftTreeMap_intertwines q hq hq1 l m n p.1 p.2) 0
  simpa only [Fin.val_zero,Nat.cast_zero,mul_zero,sub_zero] using h

theorem quantumRightTreeHighest_K (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : RightHighestPath l m n) :
    finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n (uqGenerator q 2)
      (quantumRightTreeHighest q hq hq1 l m n p.1 p.2)=
      q^(coupledLabel l (coupledLabel m n p.1) p.2:ℤ) • quantumRightTreeHighest q hq hq1 l m n p.1 p.2 := by
  have h := quantumIntertwiner_K_basis (W:=RealQuantumTripleSpace l m n) q hq hq1
    (coupledLabel l (coupledLabel m n p.1) p.2) _ _ (quantumRightTreeMap_intertwines q hq hq1 l m n p.1 p.2) 0
  simpa only [Fin.val_zero,Nat.cast_zero,mul_zero,sub_zero] using h

theorem fullRecoupling_highest_rightLower_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n)
    (k : Fin (coupledLabel l (coupledLabel m n a.1) a.2)) :
    fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) ⟨a.1,⟨a.2,k.succ⟩⟩=0 := by
  unfold fullQuantumRecouplingMatrix
  rw [leftFusionHighest_eq]
  exact quantumHighest_orthogonal_orthonormalLower (W:=RealQuantumTripleSpace l m n) q hq hq1
    (coupledLabel (coupledLabel l m p.1) n p.2) (coupledLabel l (coupledLabel m n a.1) a.2)
    (quantumTripleBilin q l m n) (quantumTripleBilin_symm q hq hq1 l m n)
    (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
    (finiteTripleRepresentation_compact q hq hq1 l m n) _
    (quantumLeftTreeHighest_E q hq hq1 l m n p) (quantumLeftTreeHighest_K q hq hq1 l m n p)
    (quantumRightTreeMap q hq hq1 l m n a.1 a.2) (quantumRightTreeMap_intertwines q hq hq1 l m n a.1 a.2) k

theorem fullRecoupling_leftLower_highest_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : RightHighestPath l m n) (a : LeftHighestPath l m n)
    (k : Fin (coupledLabel (coupledLabel l m a.1) n a.2)) :
    fullQuantumRecouplingMatrix q hq hq1 l m n ⟨a.1,⟨a.2,k.succ⟩⟩ (rightHighestEmbedding l m n p)=0 := by
  unfold fullQuantumRecouplingMatrix
  rw [rightFusionHighest_eq,quantumTripleBilin_symm q hq hq1 l m n]
  exact quantumHighest_orthogonal_orthonormalLower (W:=RealQuantumTripleSpace l m n) q hq hq1
    (coupledLabel l (coupledLabel m n p.1) p.2) (coupledLabel (coupledLabel l m a.1) n a.2)
    (quantumTripleBilin q l m n) (quantumTripleBilin_symm q hq hq1 l m n)
    (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
    (finiteTripleRepresentation_compact q hq hq1 l m n) _
    (quantumRightTreeHighest_E q hq hq1 l m n p) (quantumRightTreeHighest_K q hq hq1 l m n p)
    (quantumLeftTreeMap q hq hq1 l m n a.1 a.2) (quantumLeftTreeMap_intertwines q hq hq1 l m n a.1 a.2) k

/-- Highest-weight recoupling matrix, defined from actual isometric quantum intertwiners. -/
def quantumRacahMatrix (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    Matrix (LeftHighestPath l m n) (RightHighestPath l m n) ℝ :=
  fun p v => quantumRacahEntry q hq hq1 l m n p.1 p.2 v.1 v.2

theorem fullRecoupling_highest_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (v : RightHighestPath l m n) :
    fullQuantumRecouplingMatrix q hq hq1 l m n (leftHighestEmbedding l m n p) (rightHighestEmbedding l m n v)=
      quantumRacahMatrix q hq hq1 l m n p v := by
  unfold fullQuantumRecouplingMatrix
  rw [leftFusionHighest_eq,rightFusionHighest_eq]
  rfl

end AMSPhysical

#print axioms AMSPhysical.fullRecoupling_highest_rightLower_zero
#print axioms AMSPhysical.fullRecoupling_highest_eq

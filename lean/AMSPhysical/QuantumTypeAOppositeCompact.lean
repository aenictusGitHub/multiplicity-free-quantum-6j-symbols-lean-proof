import QuantumOccupationAdjoint
import QuantumOppositeWeight
import QuantumTypeADualForm
import QuantumTypeAPivotalWeights
import QuantumTypeARelations

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def occupationOppositeBilin (q : ℝ) (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] ℝ :=
  finiteWeightedBilin (occupationOppositeWeight q n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap

theorem occupationOppositeBilin_symm (q : ℝ) (n L : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationOppositeBilin q n L v w=occupationOppositeBilin q n L w v :=
  finiteWeightedPair_symm _ _ _ _

/-- An actual positive inner product on every constructed higher-rank module. -/
def occupationOppositeNormed (q : ℝ) (hq : 0<q) (n L : ℕ) :
    NormedAddCommGroup (quantumOccupationSpace ℝ (Fin (n+1)) L) :=
  finiteWeightedNormedAddCommGroup (occupationOppositeWeight q n L)
    (occupationOppositeWeight_pos q hq n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.injective

def occupationOppositeInner (q : ℝ) (hq : 0<q) (n L : ℕ) :
    letI := occupationOppositeNormed q hq n L
    InnerProductSpace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L) :=
  finiteWeightedInnerProductSpace (occupationOppositeWeight q n L)
    (occupationOppositeWeight_pos q hq n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.injective

theorem typeAOppositeForm_K_adjoint (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationOppositeBilin q n L) (typeAFiniteGenerator q hq hD n L i 2)
      (typeAFiniteGenerator q hq hD n L i 2) := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  rw [typeAFiniteGenerator_K_basis,typeAFiniteGenerator_K_basis,finiteWeightedPair_smul_left,
    finiteWeightedPair_smul_right,finiteWeightedPair_basis]
  split_ifs with h
  · subst y
    rfl
  · simp

theorem typeAOppositeForm_Ki_adjoint (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationOppositeBilin q n L) (typeAFiniteGenerator q hq hD n L i 3)
      (typeAFiniteGenerator q hq hD n L i 3) := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  rw [typeAFiniteGenerator_Ki_basis,typeAFiniteGenerator_Ki_basis,finiteWeightedPair_smul_left,
    finiteWeightedPair_smul_right,finiteWeightedPair_basis]
  split_ifs with h
  · subst y
    rfl
  · simp

theorem typeAOppositeForm_E_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationOppositeBilin q n L)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2) := by
  apply occupation_E_adjoint_of_edges q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i
    (occupationOppositeWeight q n L) _
    (fun x => q^(simpleOccupationWeight n x.val i+2)*qInteger q (x.val i.castSucc+1))
  · intro x hi
    rw [Module.End.mul_apply,typeAFiniteGenerator_K_basis,map_smul,typeAFiniteGenerator_F_reversed,
      smul_smul,raisedOccupation_simpleWeight]
  · intro y hy
    rw [Module.End.mul_apply,typeAFiniteGenerator_K_basis,map_smul,
      typeAFiniteGenerator_F_zero q _ _ n L y i hy,smul_zero]
  · intro x hi
    exact occupationOppositeWeight_raised q hq hq1 n L x i hi

theorem typeAOppositeForm_F_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationOppositeBilin q n L)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0) := by
  have h := ((typeAOppositeForm_E_adjoint q hq hq1 n L i).symm (occupationOppositeBilin_symm q n L)).mul
    (typeAOppositeForm_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i)
  have hinv : typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2*
      typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3=1 := by
    unfold typeAFiniteGenerator
    rw [← map_mul,uqA_inverse,map_one]
  rw [mul_assoc,hinv,mul_one] at h
  exact h

end AMSPhysical
#print axioms AMSPhysical.typeAOppositeForm_F_adjoint

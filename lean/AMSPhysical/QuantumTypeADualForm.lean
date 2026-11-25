import QuantumOccupationAdjoint
import QuantumOccupationWeights
import QuantumTypeAPivotalWeights
import QuantumTypeARelations

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def occupationDualBilin (q : ℝ) (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] ℝ :=
  finiteWeightedBilin (occupationDualWeight q n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap

theorem occupationDualBilin_symm (q : ℝ) (n L : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationDualBilin q n L v w=occupationDualBilin q n L w v := finiteWeightedPair_symm _ _ _ _

theorem raisedOccupation_simpleWeight (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    simpleOccupationWeight n (raisedOccupation n L x i hi).val i=simpleOccupationWeight n x.val i+2 := by
  unfold simpleOccupationWeight
  rw [raisedOccupation_target,raisedOccupation_source]
  ring

theorem typeADual_K_adjoint (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationDualBilin q n L) (typeAFiniteGenerator q hq hD n L i 2)
      (typeAFiniteGenerator q hq hD n L i 2) := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  rw [typeAFiniteGenerator_K_basis,typeAFiniteGenerator_K_basis,finiteWeightedPair_smul_left,
    finiteWeightedPair_smul_right,finiteWeightedPair_basis]
  split_ifs with h
  · subst y
    rfl
  · simp

theorem typeADual_Ki_adjoint (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationDualBilin q n L) (typeAFiniteGenerator q hq hD n L i 3)
      (typeAFiniteGenerator q hq hD n L i 3) := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  rw [typeAFiniteGenerator_Ki_basis,typeAFiniteGenerator_Ki_basis,finiteWeightedPair_smul_left,
    finiteWeightedPair_smul_right,finiteWeightedPair_basis]
  split_ifs with h
  · subst y
    rfl
  · simp

theorem typeADual_E_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationDualBilin q n L)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0)
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2)) := by
  apply occupation_E_adjoint_of_edges q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i
    (occupationDualWeight q n L) _
    (fun x => -q^(simpleOccupationWeight n x.val i+2)*qInteger q (x.val i.castSucc+1))
  · intro x hi
    rw [LinearMap.neg_apply,Module.End.mul_apply,typeAFiniteGenerator_K_basis,map_smul,
      typeAFiniteGenerator_F_reversed,smul_smul,raisedOccupation_simpleWeight]
    rw [← neg_smul]
    congr 1
    ring
  · intro y hy
    rw [LinearMap.neg_apply,Module.End.mul_apply,typeAFiniteGenerator_K_basis,map_smul,
      typeAFiniteGenerator_F_zero q _ _ n L y i hy,smul_zero,neg_zero]
  · intro x hi
    exact occupationDualWeight_raised q hq hq1 n L x i hi

theorem typeADual_F_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationDualBilin q n L)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1)
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0)) := by
  have h := ((typeADual_E_adjoint q hq hq1 n L i).symm (occupationDualBilin_symm q n L)).mul
    (typeADual_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i)
  have hinv : typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2*
      typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3=1 := by
    unfold typeAFiniteGenerator
    rw [← map_mul,uqA_inverse,map_one]
  have hc : -(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1*
      typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2)*
      typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3=
      -(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1) := by
    apply LinearMap.ext
    intro v
    have he := DFunLike.congr_fun hinv v
    change typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3 v)=v at he
    change -(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2
        (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3 v)))=_
    rw [he]
    rfl
  rw [hc] at h
  intro v w
  have hh := h v w
  change occupationDualBilin q n L (-(typeAFiniteGenerator q (ne_of_gt hq)
    (qInteger_denominator_ne_zero q hq hq1) n L i 1 v)) w=_ at hh
  rw [map_neg,LinearMap.neg_apply] at hh
  change -occupationDualBilin q n L (typeAFiniteGenerator q (ne_of_gt hq)
    (qInteger_denominator_ne_zero q hq hq1) n L i 1 v) w=
      occupationDualBilin q n L v (typeAFiniteGenerator q (ne_of_gt hq)
        (qInteger_denominator_ne_zero q hq hq1) n L i 3
        (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0 w)) at hh
  change occupationDualBilin q n L (typeAFiniteGenerator q (ne_of_gt hq)
    (qInteger_denominator_ne_zero q hq hq1) n L i 1 v) w=
      occupationDualBilin q n L v (-(typeAFiniteGenerator q (ne_of_gt hq)
        (qInteger_denominator_ne_zero q hq hq1) n L i 3
        (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0 w)))
  rw [map_neg]
  linarith

end AMSPhysical
#print axioms AMSPhysical.typeADual_F_adjoint

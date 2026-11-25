import QuantumDualSigns
import QuantumOccupationAdjoint
import QuantumTypeADualInvariant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def occupationReverseDualWeight (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℝ :=
  occupationDualSign n L x*occupationCompactWeight q n L x

def occupationReverseDualBilin (q : ℝ) (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] ℝ :=
  finiteWeightedBilin (occupationReverseDualWeight q n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap

theorem occupationReverseDualBilin_symm (q : ℝ) (n L : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationReverseDualBilin q n L v w=occupationReverseDualBilin q n L w v := finiteWeightedPair_symm _ _ v w

theorem typeAReverseDual_K_adjoint (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationReverseDualBilin q n L) (typeAFiniteGenerator q hq hD n L i 2)
      (typeAFiniteGenerator q hq hD n L i 2) := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  rw [typeAFiniteGenerator_K_basis,typeAFiniteGenerator_K_basis,finiteWeightedPair_smul_left,
    finiteWeightedPair_smul_right,finiteWeightedPair_basis]
  split_ifs with h
  · subst y
    rfl
  · simp

theorem typeAReverseDual_Ki_adjoint (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationReverseDualBilin q n L) (typeAFiniteGenerator q hq hD n L i 3)
      (typeAFiniteGenerator q hq hD n L i 3) := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  rw [typeAFiniteGenerator_Ki_basis,typeAFiniteGenerator_Ki_basis,finiteWeightedPair_smul_left,
    finiteWeightedPair_smul_right,finiteWeightedPair_basis]
  split_ifs with h
  · subst y
    rfl
  · simp

theorem typeAReverseDual_E_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationReverseDualBilin q n L)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0)
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1)) := by
  apply occupation_E_adjoint_of_edges q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i
    (occupationReverseDualWeight q n L) _
    (fun x => -q^(simpleOccupationWeight n x.val i)*qInteger q (x.val i.castSucc+1))
  · intro x hi
    rw [LinearMap.neg_apply,Module.End.mul_apply,typeAFiniteGenerator_F_reversed,map_smul,
      typeAFiniteGenerator_K_basis,smul_smul,← neg_smul]
    congr 1
    ring
  · intro y hy
    rw [LinearMap.neg_apply,Module.End.mul_apply,typeAFiniteGenerator_F_zero q _ _ n L y i hy,map_zero,neg_zero]
  · intro x hi
    have h:=occupationCompactWeight_raised q hq hq1 n L x i hi
    unfold occupationReverseDualWeight
    rw [occupationDualSign_raised]
    linear_combination -(occupationDualSign n L x)*h

theorem typeAReverseDual_F_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n) :
    PairAdjoint (occupationReverseDualBilin q n L)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1)
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3)) := by
  have h := (typeAReverseDual_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i).mul
    ((typeAReverseDual_E_adjoint q hq hq1 n L i).symm (occupationReverseDualBilin_symm q n L))
  have he : typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3*
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1))=
      -(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1) := by
    apply LinearMap.ext
    intro v
    change typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2
        (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1 v)))=_
    rw [map_neg]
    have hv:=DFunLike.congr_fun (typeADual_Ki_K q hq hq1 n L i)
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1 v)
    change typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3
      (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2
        (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1 v))=_ at hv
    rw [hv]
    rfl
  rw [he] at h
  intro v w
  have hh:=h v w
  change occupationReverseDualBilin q n L
    (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1 v)) w=_ at hh
  rw [map_neg,LinearMap.neg_apply] at hh
  change occupationReverseDualBilin q n L
    (typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 1 v) w=
    occupationReverseDualBilin q n L v
      (-(typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 0*
        typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3) w)
  rw [map_neg]
  linarith

end AMSPhysical

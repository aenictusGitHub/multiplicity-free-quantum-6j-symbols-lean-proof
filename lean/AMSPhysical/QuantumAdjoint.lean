import QuantumMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open Module

theorem standardWeightBasis_Kinv (q : ℝ) (L : ℕ) (k : Fin (L+1)) :
    finiteQuantumKinv q L (standardWeightBasis L k)=
      q^(-((L:ℤ)-2*(k.val:ℤ))) • standardWeightBasis L k := by
  rw [standardWeightBasis_apply]
  apply Subtype.ext
  change quantumKinv q L (Finsupp.single (k.val:ℤ) 1)=
    q^(-((L:ℤ)-2*(k.val:ℤ))) • Finsupp.single (k.val:ℤ) 1
  simp only [quantumKinv,weightShift_single,add_zero,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem quantumK_adjoint (q : ℝ) (L : ℕ) :
    PairAdjoint (quantumBilin q L) (finiteQuantumK q L) (finiteQuantumK q L) := by
  apply finiteWeightedAdjoint_of_basis (standardWeightBasis L)
  intro i j
  change quantumPair q L _ _=quantumPair q L _ _
  rw [standardWeightBasis_K,standardWeightBasis_K,quantumPair_smul_left,quantumPair_smul_right,
    quantumPair_basis]
  split_ifs with h
  · subst j
    rfl
  · simp

theorem quantumKinv_adjoint (q : ℝ) (L : ℕ) :
    PairAdjoint (quantumBilin q L) (finiteQuantumKinv q L) (finiteQuantumKinv q L) := by
  apply finiteWeightedAdjoint_of_basis (standardWeightBasis L)
  intro i j
  change quantumPair q L _ _=quantumPair q L _ _
  rw [standardWeightBasis_Kinv,standardWeightBasis_Kinv,quantumPair_smul_left,quantumPair_smul_right,
    quantumPair_basis]
  split_ifs with h
  · subst j
    rfl
  · simp

theorem quantumE_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ) :
    PairAdjoint (quantumBilin q L) (finiteQuantumE q L)
      (finiteQuantumK q L*finiteQuantumF q L) := by
  apply finiteWeightedAdjoint_of_basis (standardWeightBasis L)
  intro i j
  change quantumPair q L _ _=quantumPair q L _ _
  change quantumPair q L (finiteQuantumE q L (standardWeightBasis L i)) (standardWeightBasis L j)=
    quantumPair q L (standardWeightBasis L i)
      (finiteQuantumK q L (finiteQuantumF q L (standardWeightBasis L j)))
  refine Fin.cases ?_ (fun a => ?_) i
  · rw [standardWeightBasis_E_zero,quantumPair_zero_left]
    refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [standardWeightBasis_F_last,(finiteQuantumK q L).map_zero,quantumPair_zero_right]
    · rw [standardWeightBasis_F_castSucc,map_smul,standardWeightBasis_K,smul_smul,
        quantumPair_smul_right,quantumPair_basis,if_neg (Fin.succ_ne_zero b).symm,mul_zero]
  · rw [standardWeightBasis_E_succ,quantumPair_smul_left]
    refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [standardWeightBasis_F_last,(finiteQuantumK q L).map_zero,quantumPair_zero_right,
        quantumPair_basis,if_neg (Fin.castSucc_ne_last a),mul_zero]
    · rw [standardWeightBasis_F_castSucc,map_smul,standardWeightBasis_K,smul_smul,
        quantumPair_smul_right,quantumPair_basis,quantumPair_basis]
      by_cases hab : a=b
      · subst b
        simp only [ite_true]
        have hc : ((L:ℤ)-(a.val:ℤ))=((L-a.val:ℕ):ℤ) := by omega
        rw [hc,← qnum_eq_qInteger q hq hq1,← qnum_eq_qInteger q hq hq1]
        change qnum q (a.val+1)*quantumWeight q L a.val=
          qnum q (L-a.val)*q^((L:ℤ)-2*((a.val+1:ℕ):ℤ))*quantumWeight q L (a.val+1)
        linear_combination -(quantumWeight_step q hq L a.val a.isLt)
      · have hcs : a.castSucc≠b.castSucc := fun h => hab (Fin.castSucc_injective _ h)
        have hsu : a.succ≠b.succ := fun h => hab (Fin.succ_injective _ h)
        rw [if_neg hcs,if_neg hsu,mul_zero,mul_zero]

theorem quantumF_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ) :
    PairAdjoint (quantumBilin q L) (finiteQuantumF q L)
      (finiteQuantumE q L*finiteQuantumKinv q L) := by
  have h := (quantumKinv_adjoint q L).mul
    ((quantumE_adjoint q hq hq1 L).symm (quantumPair_symm q L))
  rw [← mul_assoc,finiteQuantumKinv_inverse q (ne_of_gt hq),one_mul] at h
  exact h

end AMSPhysical

#print axioms AMSPhysical.quantumE_adjoint

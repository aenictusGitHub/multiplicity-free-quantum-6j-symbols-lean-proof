import FiniteWeightedHilbert
import BilinearAdjoint
import FiniteWeightActions
import QuantumAnalyticCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module

theorem qfactorial_zero (q : ℝ) : qfactorial q 0=1 := by simp [qfactorial]

theorem qfactorial_succ (q : ℝ) (k : ℕ) :
    qfactorial q (k+1)=qfactorial q k*qnum q (k+1) := by
  simp only [qfactorial,Finset.prod_range_succ]

def quantumWeightExponent (L k : ℕ) : ℤ := (k:ℤ)*((k:ℤ)+1-(L:ℤ))

/-- Positive compact-quantum-group metric in the standard highest-weight basis.
The generator convention is E*=K F and F*=E K^{-1}. -/
def quantumWeight (q : ℝ) (L k : ℕ) : ℝ :=
  q^(quantumWeightExponent L k)*qfactorial q k*qfactorial q (L-k)/qfactorial q L

theorem quantumWeight_pos (q : ℝ) (hq : 0<q) (L k : ℕ) : 0<quantumWeight q L k := by
  exact div_pos (mul_pos (mul_pos (zpow_pos hq _) (qfactorial_pos q hq k))
    (qfactorial_pos q hq (L-k))) (qfactorial_pos q hq L)

theorem quantumWeight_zero (q : ℝ) (hq : 0<q) (L : ℕ) : quantumWeight q L 0=1 := by
  simp only [quantumWeight,quantumWeightExponent,Nat.cast_zero,zero_mul,zpow_zero,
    qfactorial_zero,one_mul,mul_one,Nat.sub_zero,div_self (qfactorial_ne_zero q hq L)]

theorem quantumWeight_step (q : ℝ) (hq : 0<q) (L k : ℕ) (hk : k<L) :
    quantumWeight q L (k+1)*qnum q (L-k)*q^((L:ℤ)-2*((k+1:ℕ):ℤ))=
      qnum q (k+1)*quantumWeight q L k := by
  have hsub : L-k=(L-(k+1))+1 := by omega
  have hF : qfactorial q (L-k)=qfactorial q (L-(k+1))*qnum q (L-k) := by
    conv_lhs => rw [hsub,qfactorial_succ]
    rw [← hsub]
  have hpow : q^(quantumWeightExponent L (k+1))*q^((L:ℤ)-2*((k+1:ℕ):ℤ))=
      q^(quantumWeightExponent L k) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    simp only [quantumWeightExponent,Nat.cast_add,Nat.cast_one]
    ring
  unfold quantumWeight
  rw [qfactorial_succ,hF]
  field_simp [qfactorial_ne_zero q hq L]
  linear_combination
    (qfactorial q k*qnum q (k+1)*qfactorial q (L-(k+1))*qnum q (L-k))*hpow

def quantumPair (q : ℝ) (L : ℕ) : finiteWeightSpace (K:=ℝ) L → finiteWeightSpace (K:=ℝ) L → ℝ :=
  finiteWeightedPair (fun k : Fin (L+1) => quantumWeight q L k.val)
    (standardWeightBasis L).equivFun.toLinearMap

def quantumPairCore (q : ℝ) (hq : 0<q) (L : ℕ) :
    InnerProductSpace.Core ℝ (finiteWeightSpace (K:=ℝ) L) :=
  finiteWeightedCore (fun k : Fin (L+1) => quantumWeight q L k.val)
    (fun k => quantumWeight_pos q hq L k.val) (standardWeightBasis L).equivFun.toLinearMap
    (standardWeightBasis L).equivFun.injective

theorem quantumPair_basis (q : ℝ) (L : ℕ) (i j : Fin (L+1)) :
    quantumPair q L (standardWeightBasis L i) (standardWeightBasis L j)=
      if i=j then quantumWeight q L i.val else 0 :=
  finiteWeightedPair_basis (standardWeightBasis L) _ i j

theorem quantumPair_nonneg (q : ℝ) (hq : 0<q) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L) :
    0≤quantumPair q L v v :=
  finiteWeightedPair_nonneg (V:=finiteWeightSpace (K:=ℝ) L)
    (fun k : Fin (L+1) => quantumWeight q L k.val)
    (fun k => (quantumWeight_pos q hq L k.val).le) (standardWeightBasis L).equivFun.toLinearMap v

theorem quantumPair_definite (q : ℝ) (hq : 0<q) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L)
    (hv : quantumPair q L v v=0) : v=0 :=
  finiteWeightedPair_definite (V:=finiteWeightSpace (K:=ℝ) L)
    (fun k : Fin (L+1) => quantumWeight q L k.val)
    (fun k => quantumWeight_pos q hq L k.val)
    (standardWeightBasis L).equivFun.toLinearMap (standardWeightBasis L).equivFun.injective v hv

theorem quantumPair_pos (q : ℝ) (hq : 0<q) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L)
    (hv : v≠0) : 0<quantumPair q L v v :=
  lt_of_le_of_ne (quantumPair_nonneg q hq L v) (fun he => hv (quantumPair_definite q hq L v he.symm))

def quantumBilin (q : ℝ) (L : ℕ) : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ]
    finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] ℝ :=
  finiteWeightedBilin (fun k : Fin (L+1) => quantumWeight q L k.val)
    (standardWeightBasis L).equivFun.toLinearMap

theorem quantumPair_symm (q : ℝ) (L : ℕ) (p v : finiteWeightSpace (K:=ℝ) L) :
    quantumPair q L p v=quantumPair q L v p :=
  finiteWeightedPair_symm _ (standardWeightBasis L).equivFun.toLinearMap p v

theorem quantumPair_smul_left (q : ℝ) (L : ℕ) (a : ℝ)
    (p v : finiteWeightSpace (K:=ℝ) L) :
    quantumPair q L (a • p) v=a*quantumPair q L p v :=
  finiteWeightedPair_smul_left _ (standardWeightBasis L).equivFun.toLinearMap a p v

theorem quantumPair_smul_right (q : ℝ) (L : ℕ) (a : ℝ)
    (p v : finiteWeightSpace (K:=ℝ) L) :
    quantumPair q L p (a • v)=a*quantumPair q L p v :=
  finiteWeightedPair_smul_right _ (standardWeightBasis L).equivFun.toLinearMap a p v

theorem quantumPair_zero_left (q : ℝ) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L) :
    quantumPair q L 0 v=0 := by
  exact (quantumBilin q L).map_zero |> fun h => congrArg (fun f => f v) h

theorem quantumPair_zero_right (q : ℝ) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L) :
    quantumPair q L v 0=0 := (quantumBilin q L v).map_zero

end AMSPhysical

#print axioms AMSPhysical.quantumPairCore
#print axioms AMSPhysical.quantumWeight_step

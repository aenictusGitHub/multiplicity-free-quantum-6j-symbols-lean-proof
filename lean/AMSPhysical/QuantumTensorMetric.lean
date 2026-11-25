import QuantumAdjoint
import TensorQuantumCompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def quantumTensorBilin (q : ℝ) (l m : ℕ) :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ]
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ] ℝ :=
  tensorWeightedBilin (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m)
    (fun k => quantumWeight q l k.val) (fun k => quantumWeight q m k.val)

theorem finiteQuantum_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ) :
    IsCompactQuantumPair (V:=finiteWeightSpace (K:=ℝ) L) q (quantumBilin q L)
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) := by
  have hg (i : Fin 4) : finiteQuantumRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q i)=
      ![finiteQuantumE q L,finiteQuantumF q L,finiteQuantumK q L,finiteQuantumKinv q L] i :=
    finiteQuantumRepresentation_generator q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L i
  constructor
  · rw [hg 0,hg 2,hg 1]
    exact quantumE_adjoint q hq hq1 L
  · rw [hg 1,hg 0,hg 3]
    exact quantumF_adjoint q hq hq1 L
  · rw [hg 2]
    exact quantumK_adjoint q L
  · rw [hg 3]
    exact quantumKinv_adjoint q L

theorem finiteQuantumTensor_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) :
    IsCompactQuantumPair (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) q (quantumTensorBilin q l m)
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m) := by
  exact compactQuantumPair_tensor (V:=finiteWeightSpace (K:=ℝ) l) (W:=finiteWeightSpace (K:=ℝ) m)
    q (ne_of_gt hq) (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m)
    (fun k => quantumWeight q l k.val) (fun k => quantumWeight q m k.val)
    (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l)
    (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) m)
    (finiteQuantum_compact q hq hq1 l) (finiteQuantum_compact q hq hq1 m)

theorem quantumTensorBilin_tmul (q : ℝ) (l m : ℕ)
    (p p' : finiteWeightSpace (K:=ℝ) l) (v v' : finiteWeightSpace (K:=ℝ) m) :
    quantumTensorBilin q l m (p ⊗ₜ[ℝ] v) (p' ⊗ₜ[ℝ] v')=
      quantumPair q l p p'*quantumPair q m v v' :=
  tensorWeightedBilin_tmul (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m) _ _ p p' v v'

theorem quantumTensorBilin_nonneg (q : ℝ) (hq : 0<q) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    0≤quantumTensorBilin q l m v v := by
  unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin
  exact finiteWeightedPair_nonneg (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (fun ij : Fin (l+1) × Fin (m+1) => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val)
    (fun ij => mul_nonneg (quantumWeight_pos q hq l ij.1.val).le (quantumWeight_pos q hq m ij.2.val).le)
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m)).equivFun.toLinearMap v

theorem quantumTensorBilin_definite (q : ℝ) (hq : 0<q) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (hv : quantumTensorBilin q l m v v=0) : v=0 := by
  unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin at hv
  simp only [LinearMap.mk₂_apply] at hv
  exact finiteWeightedPair_definite (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (fun ij : Fin (l+1) × Fin (m+1) => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val)
    (fun ij => mul_pos (quantumWeight_pos q hq l ij.1.val) (quantumWeight_pos q hq m ij.2.val))
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m)).equivFun.toLinearMap
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m)).equivFun.injective v hv

theorem quantumTensorBilin_pos (q : ℝ) (hq : 0<q) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) (hv : v≠0) :
    0<quantumTensorBilin q l m v v :=
  lt_of_le_of_ne (quantumTensorBilin_nonneg q hq l m v)
    (fun he => hv (quantumTensorBilin_definite q hq l m v he.symm))

end AMSPhysical

#print axioms AMSPhysical.finiteQuantumTensor_compact

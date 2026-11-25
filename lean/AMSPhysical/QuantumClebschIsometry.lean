import QuantumIntertwinerMetric
import QuantumTensorMetric
import QuantumClebschIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def quantumHighestNorm (q : ℝ) (l m : ℕ) (r : Fin (min l m+1)) : ℝ :=
  quantumTensorBilin q l m
    (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r))
    (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r))

theorem quantumHighestNorm_pos (q : ℝ) (hq : 0<q) (l m : ℕ) (r : Fin (min l m+1)) :
    0<quantumHighestNorm q l m r :=
  quantumTensorBilin_pos q hq l m _
    (finiteCoupledHighest_ne_zero q l m r (channel_left_bound l m r) (channel_right_bound l m r))

theorem quantumClebschMap_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) 0)=
      finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r) := by
  rw [quantumClebschMap_basis]
  exact normalizedString_zero q _ _ _

theorem quantumClebschMap_metric (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (p v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    quantumTensorBilin q l m (quantumClebschMap q hq hq1 l m r p) (quantumClebschMap q hq hq1 l m r v)=
      quantumHighestNorm q l m r*quantumPair q (coupledLabel l m r) p v := by
  have h := quantumIntertwiner_metric
    (W:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    q hq hq1 (coupledLabel l m r) (quantumTensorBilin q l m)
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
    (finiteQuantumTensor_compact q hq hq1 l m) (quantumClebschMap q hq hq1 l m r)
    (quantumClebschMap_intertwines q hq hq1 l m r) p v
  rw [quantumClebschMap_highest] at h
  exact h

def unitaryQuantumClebschMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) : finiteWeightSpace (K:=ℝ) (coupledLabel l m r) →ₗ[ℝ]
      finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m :=
  (Real.sqrt (quantumHighestNorm q l m r))⁻¹ • quantumClebschMap q hq hq1 l m r

theorem unitaryQuantumClebschMap_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (p v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    quantumTensorBilin q l m (unitaryQuantumClebschMap q hq hq1 l m r p)
      (unitaryQuantumClebschMap q hq hq1 l m r v)=quantumPair q (coupledLabel l m r) p v := by
  have hN := quantumHighestNorm_pos q hq l m r
  have hs := Real.sq_sqrt hN.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hN)
  simp only [unitaryQuantumClebschMap,LinearMap.smul_apply,map_smul,smul_eq_mul,
    quantumClebschMap_metric q hq hq1]
  field_simp
  rw [hs]

theorem unitaryQuantumClebschMap_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) : Function.Injective (unitaryQuantumClebschMap q hq hq1 l m r) := by
  intro p v hpv
  have hv0 : unitaryQuantumClebschMap q hq hq1 l m r (p-v)=0 := by rw [map_sub,hpv,sub_self]
  have he := unitaryQuantumClebschMap_isometry q hq hq1 l m r (p-v) (p-v)
  rw [hv0,(quantumTensorBilin q l m).map_zero,LinearMap.zero_apply] at he
  exact sub_eq_zero.mp (quantumPair_definite q hq (coupledLabel l m r) (p-v) he.symm)

theorem unitaryQuantumClebschMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    IsQuantumIntertwiner (K:=ℝ) (V:=finiteWeightSpace (K:=ℝ) (coupledLabel l m r))
      (W:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (coupledLabel l m r))
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
      (unitaryQuantumClebschMap q hq hq1 l m r) := by
  intro x v
  simp only [unitaryQuantumClebschMap,LinearMap.smul_apply,map_smul,
    quantumClebschMap_intertwines q hq hq1 l m r x v]

end AMSPhysical

#print axioms AMSPhysical.unitaryQuantumClebschMap_isometry
#print axioms AMSPhysical.unitaryQuantumClebschMap_intertwines

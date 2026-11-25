import QuantumForgetIntertwiner
import QuantumHighestNorm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def quantumCoupledExpansion (q : ℝ) (l m : ℤ) (r a : ℕ) : WeightModule ℝ ⊗[ℝ] WeightModule ℝ :=
  ∑ k∈Finset.range (r+1),∑ t∈Finset.range (a+1),
    (couplingCoefficient q m r k*gaussianBinomial (q^2) a t*q^(-(t:ℤ)*(l-2*(k:ℤ)))*
      qFalling q (l-(k:ℤ)) (a-t)*qFalling q (m-(r:ℤ)+(k:ℤ)) t) •
      tensorWeightBasis ((k:ℤ)+((a-t:ℕ):ℤ)) ((r:ℤ)-(k:ℤ)+(t:ℤ))

theorem tensorQuantumF_power_highest (q : ℝ) (hq : q≠0) (l m : ℤ) (r a : ℕ) :
    ((tensorQuantumF q l m)^a) (coupledHighest q m r)=quantumCoupledExpansion q l m r a := by
  unfold coupledHighest quantumCoupledExpansion
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul,tensorQuantumF_power_basis q hq,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]
  congr 1
  have he : m-((r:ℤ)-(k:ℤ))=m-(r:ℤ)+(k:ℤ) := by ring
  rw [he]
  ring

theorem coupledString_closed_expansion (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (a : ℕ) :
    finiteTensorForget l m (coupledString q hq hd l m r hl hm a)=quantumCoupledExpansion q l m r a := by
  rw [coupledString_forget,tensorQuantumF_power_highest q hq]

theorem quantumClebschMap_closed_expansion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) :
    finiteTensorForget l m (quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) a))=
      (qFalling q (coupledLabel l m r) a.val)⁻¹ • quantumCoupledExpansion q l m r.val a.val := by
  rw [quantumClebschMap_basis]
  change finiteTensorForget l m
    ((qFalling q (coupledLabel l m r) a.val)⁻¹ • coupledString q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) l m r.val (channel_left_bound l m r) (channel_right_bound l m r) a.val)=_
  rw [map_smul,coupledString_closed_expansion]

theorem unitaryQuantumClebschMap_closed_expansion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) :
    finiteTensorForget l m (unitaryQuantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) a))=
      ((Real.sqrt (couplingNormClosed q (l-r.val) (m-r.val) r.val))⁻¹*
        (qFalling q (coupledLabel l m r) a.val)⁻¹) • quantumCoupledExpansion q l m r.val a.val := by
  unfold unitaryQuantumClebschMap
  rw [LinearMap.smul_apply,map_smul,quantumClebschMap_closed_expansion,smul_smul,quantumHighestNorm_closed q hq hq1]

end AMSPhysical

#print axioms AMSPhysical.unitaryQuantumClebschMap_closed_expansion

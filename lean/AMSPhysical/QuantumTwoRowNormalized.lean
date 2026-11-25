import TwoRowHighestWeight
import QuantumSymmetricMetric
import QuantumClebschAnalytic
import CompactHighestRealization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def normalizedTwoRowHighest (q : ℝ) (n : ℕ) (hn : 0<n) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  (Real.sqrt (couplingNormClosed q (l-r) (m-r) r))⁻¹ • twoRowHighest q n hn l m r hl hm

theorem normalizedTwoRowHighest_norm_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    symmetricTensorBilin q n l m (normalizedTwoRowHighest q n hn l m r hl hm)
      (normalizedTwoRowHighest q n hn l m r hl hm)=1 := by
  unfold normalizedTwoRowHighest
  simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  rw [twoRowHighest_norm_closed q hq hq1]
  have hp:=couplingNormClosed_pos q hq (l-r) (m-r) r
  have hs:=Real.sq_sqrt hp.le
  have hs0:=ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hs0]
  nlinarith

theorem normalizedTwoRowHighest_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (i : Fin n) :
    typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
      (typeAAlgebraGenerator q n i 0) (normalizedTwoRowHighest q n hn l m r hl hm)=0 := by
  rw [normalizedTwoRowHighest,map_smul,twoRowHighest_E_zero q hq hq1,smul_zero]

theorem normalizedTwoRowHighest_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (i : Fin n) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (normalizedTwoRowHighest q n hn l m r hl hm)=
      q^(twoRowHighestWeight n hn l m r i) • normalizedTwoRowHighest q n hn l m r hl hm := by
  rw [normalizedTwoRowHighest,map_smul,twoRowHighest_K,smul_comm]

theorem twoRowHighestWeight_total (n : ℕ) (hn : 0<n) (S l m r : ℕ) (hS : l+m=S) :
    twoRowHighestWeight n hn l m r=twoRowHighestWeight n hn S 0 r := by
  unfold twoRowHighestWeight twoRowOccupationWeight
  simp only [hS,Nat.add_zero]

def twoRowHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m) :
    CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (twoRowHighestWeight n hn S 0 r) where
  action := typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
  pairing := symmetricTensorBilin q n l m
  highest := normalizedTwoRowHighest q n hn l m r hl hm
  compact := typeASymmetricTensor_compact q hq hq1 n l m
  symmetric := symmetricTensorBilin_symm q n l m
  definite := symmetricTensorBilin_definite q hq n l m
  highestE := normalizedTwoRowHighest_E_zero q hq hq1 n hn l m r hl hm
  highestK := by
    intro i
    rw [normalizedTwoRowHighest_K,twoRowHighestWeight_total n hn S l m r hS]
  highestNorm := normalizedTwoRowHighest_norm_one q hq hq1 n hn l m r hl hm

def normalizedTwoRowChannel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  algebraCyclicSpan
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeASymmetricTensor q hq hD n l m) (normalizedTwoRowHighest q n hn l m r hl hm)

end AMSPhysical

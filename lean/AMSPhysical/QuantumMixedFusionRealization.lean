import QuantumMixedHighestRealizations
import QuantumMixedFusionNorm
import QuantumMixedFusionEquiv
import CyclicSpanScale

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def normalizedMixedFusionHighestAt (q : ℝ) (n l m : ℕ) (r : MixedFusionIndex l m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  (Real.sqrt (mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val))⁻¹ • mixedFusionHighestAt q n l m r

theorem normalizedMixedFusionHighestAt_norm_one (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedTensorBilin q n l m (normalizedMixedFusionHighestAt q n l m r) (normalizedMixedFusionHighestAt q n l m r)=1 := by
  unfold normalizedMixedFusionHighestAt
  simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  rw [mixedFusionHighestAt_norm_closed q hq n hn]
  have hp:=mixedCouplingNormClosed_pos q hq n (l-r.val) (m-r.val) r.val
  have hs:=Real.sq_sqrt hp.le
  have hs0:=ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hs0]
  nlinarith

def mixedFusionHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (mixedHighestDynkin n (l-r.val) (m-r.val)) where
  action := typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
  pairing := mixedTensorBilin q n l m
  highest := normalizedMixedFusionHighestAt q n l m r
  compact := typeAMixedTensor_compact q hq hq1 n l m
  symmetric := mixedTensorBilin_symm q n l m
  definite := mixedTensorBilin_definite q hq n l m
  highestE := by
    intro i
    rw [normalizedMixedFusionHighestAt,map_smul,mixedFusionHighestAt_E_zero q hq hq1,smul_zero]
  highestK := by
    intro i
    rw [normalizedMixedFusionHighestAt,map_smul,mixedFusionHighestAt_K,smul_comm]
  highestNorm := normalizedMixedFusionHighestAt_norm_one q hq n hn l m r

theorem mixedFusionHighestRealization_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    (mixedFusionHighestRealization q hq hq1 n hn l m r).channel=
      mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply algebraCyclicSpan_smul (V:=V)
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n (l-r.val) (m-r.val) r.val)))

end AMSPhysical

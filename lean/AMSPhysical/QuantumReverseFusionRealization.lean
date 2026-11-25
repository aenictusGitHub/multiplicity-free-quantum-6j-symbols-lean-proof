import QuantumMixedFusionRealization
import QuantumReverseFusionHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def normalizedReverseMixedFusionHighestAt (q : ℝ) (n l m : ℕ) (r : MixedFusionIndex l m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  (Real.sqrt (mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val))⁻¹ • reverseMixedFusionHighestAt q n l m r

theorem normalizedReverseMixedFusionHighestAt_norm_one (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    reverseMixedTensorBilin q n l m (normalizedReverseMixedFusionHighestAt q n l m r)
      (normalizedReverseMixedFusionHighestAt q n l m r)=1 := by
  unfold normalizedReverseMixedFusionHighestAt
  simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  rw [reverseMixedFusionHighestAt_norm q hq n hn]
  have hp:=mixedCouplingNormClosed_pos q hq n (l-r.val) (m-r.val) r.val
  have hs:=Real.sq_sqrt hp.le
  have hs0:=ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hs0]
  nlinarith

def reverseMixedFusionHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (mixedHighestDynkin n (m-r.val) (l-r.val)) where
  action := typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
  pairing := reverseMixedTensorBilin q n l m
  highest := normalizedReverseMixedFusionHighestAt q n l m r
  compact := typeAReverseMixedTensor_compact q hq hq1 n l m
  symmetric := reverseMixedTensorBilin_symm q n l m
  definite := reverseMixedTensorBilin_definite q hq n l m
  highestE := by
    intro i
    rw [normalizedReverseMixedFusionHighestAt,map_smul,reverseMixedFusionHighestAt_E_zero q hq hq1,smul_zero]
  highestK := by
    intro i
    rw [normalizedReverseMixedFusionHighestAt,map_smul,reverseMixedFusionHighestAt_K,smul_comm]
  highestNorm := normalizedReverseMixedFusionHighestAt_norm_one q hq n hn l m r

theorem reverseMixedFusionHighestRealization_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    (reverseMixedFusionHighestRealization q hq hq1 n hn l m r).channel=
      reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply algebraCyclicSpan_smul (V:=V)
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n (l-r.val) (m-r.val) r.val)))

def mixedFusionSwapIndex {l m : ℕ} (r : MixedFusionIndex l m) : MixedFusionIndex m l :=
  ⟨r.val,by simpa only [min_comm] using r.isLt⟩

theorem mixedFusionSwapIndex_twice {l m : ℕ} (r : MixedFusionIndex l m) :
    mixedFusionSwapIndex (mixedFusionSwapIndex r)=r := by rfl

theorem mixedFusionSwapIndex_injective {l m : ℕ} :
    Function.Injective (@mixedFusionSwapIndex l m) := by
  intro r s h
  apply Fin.ext
  exact congrArg (fun x : MixedFusionIndex m l =>x.val) h

end AMSPhysical
#print axioms AMSPhysical.reverseMixedFusionHighestRealization_channel

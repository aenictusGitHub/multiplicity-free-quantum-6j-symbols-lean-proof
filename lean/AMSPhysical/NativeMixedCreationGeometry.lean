import GlobalTypeIIRightStep
import GlobalReverseMixedPairTransfers
import QuantumMixedInputSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFiniteCreation_gram_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hw : w∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r) :
    mixedTensorBilin q n (l+1) (m+1) (mixedFiniteCreation q n l m v) (mixedFiniteCreation q n l m w)=
      mixedCreationSpectralScalar q n l m r.val*mixedTensorBilin q n l m v w := by
  rw [mixedFiniteContraction_adjoint q hq,mixedFiniteContractionCreation_channel q hq hq1 n hn l m r w hw,
    map_smul,smul_eq_mul]

theorem reverseMixedFiniteCreation_mem_successor_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hv : v∈reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r) :
    reverseMixedFiniteCreation q n l m v∈reverseMixedFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) (mixedFusionIndexSucc l m r) := by
  rw [← reverseMixedFusionChannelAt_map] at hv ⊢
  obtain ⟨v,hv,rfl⟩:=hv
  refine ⟨mixedFiniteCreation q n l m v,
    mixedFiniteCreation_mem_successor_channel q hq hq1 n hn l m r v hv,?_⟩
  simp only [reverseMixedFiniteCreation,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem reverseMixedFiniteCreation_gram_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hw : w∈reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r) :
    reverseMixedTensorBilin q n (l+1) (m+1)
      (reverseMixedFiniteCreation q n l m v) (reverseMixedFiniteCreation q n l m w)=
      mixedCreationSpectralScalar q n l m r.val*reverseMixedTensorBilin q n l m v w := by
  rw [← reverseMixedFusionChannelAt_map] at hw
  obtain ⟨w,hw,rfl⟩:=hw
  obtain ⟨v,rfl⟩:=(mixedReflection n l m).surjective v
  simp only [reverseMixedFiniteCreation,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [mixedReflection_isometry q (ne_of_gt hq),mixedReflection_isometry q (ne_of_gt hq)]
  exact mixedFiniteCreation_gram_channel q hq hq1 n hn l m r v w hw

end AMSPhysical
#print axioms AMSPhysical.reverseMixedFiniteCreation_gram_channel

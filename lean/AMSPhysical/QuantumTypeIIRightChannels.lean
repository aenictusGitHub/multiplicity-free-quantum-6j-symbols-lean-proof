import QuantumTypeIICompleteEquiv
import QuantumMixedCommutorChannels
import QuantumTripleChannelsActual
import TensorSubmoduleTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIRightIndex (a b c : ℕ) (t : QuantumCupIndex a c b) : MixedFusionIndex b c :=
  mixedFusionSwapIndex (physicalTypeIRightIndex a c 0 b t)

def physicalTypeIIRightChannel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a b c : ℕ)
    (t : QuantumCupIndex a c b) : Submodule ℝ (quantumOccupationTripleSpace n a b c) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) a))
    (mixedFusionChannelAt q hq hD n b c (typeIIRightIndex a b c t)).subtype)

theorem physicalTypeIIToI_right_channel_map (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c : ℕ) (t : QuantumCupIndex a c b) :
    (physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t).map
      (physicalTypeIIToI q hq hq1 n hn a b c).toLinearMap=
    physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n a c b (physicalTypeIRightIndex a c 0 b t) := by
  rw [physicalTripleRightChannelGeneral_actual q hq hq1 n hn]
  apply tensorRightChannel_equiv_map (physicalMixedCommutor q hq hq1 n hn b c)
  rw [physicalMixedCommutor_channel_map]
  exact congrArg (reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c b)
    (mixedFusionSwapIndex_twice (physicalTypeIRightIndex a c 0 b t))

theorem physicalTypeIIToCompleteI_right_mem_iff (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :
    physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal v∈
      physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a c 0 b t ↔
    v.val∈physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t := by
  change (physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal v).val∈
    physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n a c b (physicalTypeIRightIndex a c 0 b t) ↔ _
  rw [physicalTypeIIToCompleteI_val,← physicalTypeIIToI_right_channel_map q hq hq1 n hn a b c t]
  constructor
  · rintro ⟨w,hw,he⟩
    have hh : w=v.val:=(physicalTypeIIToI q hq hq1 n hn a b c).injective he
    rwa [hh] at hw
  · intro hv
    exact ⟨v.val,hv,rfl⟩

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIToCompleteI_right_mem_iff

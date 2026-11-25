import QuantumMixedReflection
import QuantumMixedFusionEquiv
import CyclicTwistedEquivalence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def reverseMixedFusionHighestAt (q : ℝ) (n l m : ℕ) (r : MixedFusionIndex l m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  mixedReflection n l m (mixedFusionHighestAt q n l m r)

def reverseMixedFusionChannelAt (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) (r : MixedFusionIndex l m) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  algebraCyclicSpan
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeAReverseMixedTensor q hq hD n l m) (reverseMixedFusionHighestAt q n l m r)

theorem reverseMixedFusionChannelAt_map (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (r : MixedFusionIndex l m) :
    (mixedFusionChannelAt q hq hD n l m r).map (mixedReflection n l m).toLinearMap=
      reverseMixedFusionChannelAt q hq hD n l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact cyclic_map_of_twisted_equivalence (V:=V) (W:=V)
    (typeAMixedTensor q hq hD n l m) (typeAReverseMixedTensor q hq hD n l m)
    (typeADynkinReflection q n) (typeADynkinReflection_involutive q n).surjective
    (mixedReflection n l m) (mixedReflection_intertwines q hq hD n l m) (mixedFusionHighestAt q n l m r)

/-- Complete physical fusion in the previously missing opposite/symmetric
tensor ordering, transferred by the proved actual isometric Dynkin reflection. -/
theorem reverseMixedFusionSpan_eq_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (⨆ r : MixedFusionIndex l m,reverseMixedFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m r)=⊤ := by
  simp_rw [← reverseMixedFusionChannelAt_map]
  rw [← Submodule.map_iSup]
  change (mixedFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m).map
    (mixedReflection n l m).toLinearMap=⊤
  rw [mixedFusionSpan_eq_top q hq hq1 n hn]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (mixedReflection n l m).surjective

theorem reverseMixedFusionChannels_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r s : MixedFusionIndex l m) (hrs : r≠s)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hv : v∈reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (hw : w∈reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m s) :
    reverseMixedTensorBilin q n l m v w=0 := by
  rw [← reverseMixedFusionChannelAt_map] at hv hw
  obtain ⟨v,hv,rfl⟩ := hv
  obtain ⟨w,hw,rfl⟩ := hw
  change reverseMixedTensorBilin q n l m (mixedReflection n l m v) (mixedReflection n l m w)=0
  rw [mixedReflection_isometry q (ne_of_gt hq)]
  exact mixedFusionChannels_orthogonal q hq hq1 n hn l m r s hrs hw v hv

end AMSPhysical
#print axioms AMSPhysical.reverseMixedFusionSpan_eq_top

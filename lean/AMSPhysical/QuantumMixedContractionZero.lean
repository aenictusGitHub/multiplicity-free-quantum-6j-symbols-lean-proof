import QuantumMixedContractionSpectrum
import QuantumMixedOutsideHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedFusionIndexZero (l m : ℕ) : MixedFusionIndex l m := ⟨0,by omega⟩

theorem mixedFiniteContraction_zero_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    mixedFiniteContraction q hq n l m
      (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexZero (l+1) (m+1)))=0 := by
  apply mixedHighest_zero_of_disjoint_first_weight q hq hq1 n hn l m
    (mixedHighestDynkin n (l+1) (m+1) ⟨0,hn⟩)
  · intro i
    rw [← mixedFiniteContraction_intertwines q hq hq1 n l m,
      mixedFusionHighestAt_E_zero q hq hq1,map_zero]
  · rw [← mixedFiniteContraction_intertwines q hq hq1 n l m,mixedFusionHighestAt_K,map_smul]
    simp only [mixedFusionIndexZero,Nat.sub_zero]
  · exact mixedFirstWeight_below_creation n hn l m

/-- The entire zero-contraction physical irrep is killed by the actual
contraction map, proved from the excluded highest weight. -/
theorem mixedFiniteContraction_zero_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (hv : v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (l+1) (m+1) (mixedFusionIndexZero (l+1) (m+1))) :
    mixedFiniteContraction q hq n l m v=0 := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact intertwiner_zero_on_cyclic (V:=W) (W:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFiniteContraction q hq n l m)
    (mixedFiniteContraction_intertwines q hq hq1 n l m)
    (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexZero (l+1) (m+1)))
    (mixedFiniteContraction_zero_highest q hq hq1 n hn l m) v hv

theorem mixedFiniteCreationContraction_zero_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (hv : v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (l+1) (m+1) (mixedFusionIndexZero (l+1) (m+1))) :
    mixedFiniteCreation q n l m (mixedFiniteContraction q hq n l m v)=0 := by
  rw [mixedFiniteContraction_zero_channel q hq hq1 n hn l m v hv,map_zero]

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreationContraction_zero_channel

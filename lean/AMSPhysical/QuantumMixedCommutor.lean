import QuantumReverseFusionRealization
import OrthogonalFusionTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedCommutorSourceRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :=
  mixedFusionHighestRealization q hq hq1 n hn l m r

def mixedCommutorTargetRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :=
  reverseMixedFusionHighestRealization q hq hq1 n hn m l (mixedFusionSwapIndex r)

theorem mixedCommutorSource_span (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (⨆ r : MixedFusionIndex l m,(mixedCommutorSourceRealization q hq hq1 n hn l m r).channel)=⊤ := by
  simp only [mixedCommutorSourceRealization,mixedFusionHighestRealization_channel]
  exact mixedFusionSpan_eq_top q hq hq1 n hn l m

theorem mixedCommutorTarget_span (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (⨆ r : MixedFusionIndex l m,(mixedCommutorTargetRealization q hq hq1 n hn l m r).channel)=⊤ := by
  simp only [mixedCommutorTargetRealization,reverseMixedFusionHighestRealization_channel]
  apply le_antisymm le_top
  rw [← reverseMixedFusionSpan_eq_top q hq hq1 n hn m l]
  apply iSup_le
  intro r
  exact le_iSup_of_le (mixedFusionSwapIndex r) (by rw [mixedFusionSwapIndex_twice])

theorem mixedCommutorSource_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (i j : MixedFusionIndex l m) (hij : i≠j)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hx : x∈(mixedCommutorSourceRealization q hq hq1 n hn l m i).channel)
    (y : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hy : y∈(mixedCommutorSourceRealization q hq hq1 n hn l m j).channel) :
    mixedTensorBilin q n l m x y=0 := by
  simp only [mixedCommutorSourceRealization,mixedFusionHighestRealization_channel] at hx hy
  exact mixedFusionChannels_orthogonal q hq hq1 n hn l m i j hij hy x hx

theorem mixedCommutorTarget_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (i j : MixedFusionIndex l m) (hij : i≠j)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l)
    (hx : x∈(mixedCommutorTargetRealization q hq hq1 n hn l m i).channel)
    (y : quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l)
    (hy : y∈(mixedCommutorTargetRealization q hq hq1 n hn l m j).channel) :
    reverseMixedTensorBilin q n m l x y=0 := by
  simp only [mixedCommutorTargetRealization,reverseMixedFusionHighestRealization_channel] at hx hy
  exact reverseMixedFusionChannels_orthogonal q hq hq1 n hn m l
    (mixedFusionSwapIndex i) (mixedFusionSwapIndex j) (fun he =>hij (mixedFusionSwapIndex_injective he)) x y hx hy

/-- An actual compact isometric module commutor, assembled from the complete
physical fusion channels. No braiding or hexagon identity is postulated. -/
def physicalMixedCommutor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) ≃ₗ[ℝ]
    (quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  exact orthogonalFusionTransport (V:=V) (W:=W)
    (mixedTensorBilin q n l m) (reverseMixedTensorBilin q n m l)
    (mixedTensorBilin_definite q hq n l m) (reverseMixedTensorBilin_definite q hq n m l)
    (fun r =>(mixedCommutorSourceRealization q hq hq1 n hn l m r).channel)
    (fun r =>(mixedCommutorTargetRealization q hq hq1 n hn l m r).channel)
    (mixedCommutorSource_orthogonal q hq hq1 n hn l m)
    (mixedCommutorTarget_orthogonal q hq hq1 n hn l m)
    (mixedCommutorSource_span q hq hq1 n hn l m)
    (mixedCommutorTarget_span q hq hq1 n hn l m)
    (fun r =>CompactHighestRealization.transport (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn l m r)
      (mixedCommutorTargetRealization q hq hq1 n hn l m r))

theorem physicalMixedCommutor_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (x y : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    reverseMixedTensorBilin q n m l (physicalMixedCommutor q hq hq1 n hn l m x)
      (physicalMixedCommutor q hq hq1 n hn l m y)=mixedTensorBilin q n l m x y := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  exact orthogonalFusionTransport_isometry (V:=V) (W:=W)
    (mixedTensorBilin q n l m) (reverseMixedTensorBilin q n m l)
    (mixedTensorBilin_definite q hq n l m) (reverseMixedTensorBilin_definite q hq n m l)
    (fun r =>(mixedCommutorSourceRealization q hq hq1 n hn l m r).channel)
    (fun r =>(mixedCommutorTargetRealization q hq hq1 n hn l m r).channel)
    (mixedCommutorSource_orthogonal q hq hq1 n hn l m)
    (mixedCommutorTarget_orthogonal q hq hq1 n hn l m)
    (mixedCommutorSource_span q hq hq1 n hn l m)
    (mixedCommutorTarget_span q hq hq1 n hn l m)
    (fun r =>CompactHighestRealization.transport (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn l m r)
      (mixedCommutorTargetRealization q hq hq1 n hn l m r))
    (fun r u v =>(CompactHighestRealization.transport_isometry (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn l m r)
      (mixedCommutorTargetRealization q hq hq1 n hn l m r) u v).symm) x y

theorem physicalMixedCommutor_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (z : UqTypeA q n)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    physicalMixedCommutor q hq hq1 n hn l m
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z x)=
    typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m l z
      (physicalMixedCommutor q hq hq1 n hn l m x) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  exact orthogonalFusionTransport_intertwines (V:=V) (W:=W)
    (mixedTensorBilin q n l m) (reverseMixedTensorBilin q n m l)
    (mixedTensorBilin_definite q hq n l m) (reverseMixedTensorBilin_definite q hq n m l)
    (fun r =>(mixedCommutorSourceRealization q hq hq1 n hn l m r).channel)
    (fun r =>(mixedCommutorTargetRealization q hq hq1 n hn l m r).channel)
    (mixedCommutorSource_orthogonal q hq hq1 n hn l m)
    (mixedCommutorTarget_orthogonal q hq hq1 n hn l m)
    (mixedCommutorSource_span q hq hq1 n hn l m)
    (mixedCommutorTarget_span q hq hq1 n hn l m)
    (fun r =>CompactHighestRealization.transport (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn l m r)
      (mixedCommutorTargetRealization q hq hq1 n hn l m r))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m l)
    (fun _ =>algebraCyclicSpan_invariant _ _)
    (fun _ =>algebraCyclicSpan_invariant _ _)
    (fun r a v =>CompactHighestRealization.transport_intertwines (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn l m r)
      (mixedCommutorTargetRealization q hq hq1 n hn l m r) a v) z x

end AMSPhysical
#print axioms AMSPhysical.physicalMixedCommutor_intertwines
#print axioms AMSPhysical.physicalMixedCommutor_isometry

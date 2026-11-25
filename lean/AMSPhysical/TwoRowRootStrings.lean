import TwoVertexPairLowering
import QuantumTwoRowNormalized
import QuantumHighestNorm
import FiniteLoweringCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The concrete first-root sl2 string inside an actual higher-rank two-row
channel, with its independent standard compact normalization. -/
def twoRowRootStringEmbedding (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    finiteWeightSpace (K:=ℝ) (coupledLabel l m r) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  (twoVertexTensorEmbedding n hn l m).comp (unitaryQuantumClebschMap q hq hq1 l m r)

theorem twoRowRootStringEmbedding_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    twoRowRootStringEmbedding q hq hq1 n hn l m r (standardWeightBasis (coupledLabel l m r) 0)=
      normalizedTwoRowHighest q n hn l m r.val (channel_left_bound l m r) (channel_right_bound l m r) := by
  unfold twoRowRootStringEmbedding unitaryQuantumClebschMap
  rw [LinearMap.comp_apply,LinearMap.smul_apply,quantumClebschMap_highest,map_smul,quantumHighestNorm_closed q hq hq1]
  rfl

theorem twoRowRootStringEmbedding_F (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m)
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    twoRowRootStringEmbedding q hq hq1 n hn l m r (finiteQuantumF q (coupledLabel l m r) v)=
      typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
        (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1)
        (twoRowRootStringEmbedding q hq hq1 n hn l m r v) := by
  have he:=unitaryQuantumClebschMap_intertwines q hq hq1 l m r (uqGenerator q 1) v
  simp only [uqGenerator,finiteQuantumRepresentation_generator] at he
  change _=unitaryQuantumClebschMap q hq hq1 l m r (finiteQuantumF q (coupledLabel l m r) v) at he
  unfold twoRowRootStringEmbedding
  simp only [LinearMap.comp_apply]
  rw [← he]
  exact twoVertexTensorEmbedding_F q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m _

theorem twoRowRootStringEmbedding_mem_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m)
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    twoRowRootStringEmbedding q hq hq1 n hn l m r v∈
      normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        n hn l m r.val (channel_left_bound l m r) (channel_right_bound l m r) := by
  refine finiteQuantumF_range_mem
    (W:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    q hq hq1 (coupledLabel l m r)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
      (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1))
    (twoRowRootStringEmbedding q hq hq1 n hn l m r)
    (twoRowRootStringEmbedding_F q hq hq1 n hn l m r)
    (normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n hn l m r.val (channel_left_bound l m r) (channel_right_bound l m r)) ?_ ?_ v
  · intro w hw
    exact algebraCyclicSpan_invariant _ _ _ w hw
  · rw [twoRowRootStringEmbedding_highest]
    exact algebraCyclicSpan_self _ _

theorem twoRowRootStringEmbedding_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m)
    (v w : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    symmetricTensorBilin q n l m (twoRowRootStringEmbedding q hq hq1 n hn l m r v)
      (twoRowRootStringEmbedding q hq hq1 n hn l m r w)=quantumPair q (coupledLabel l m r) v w := by
  unfold twoRowRootStringEmbedding
  simp only [LinearMap.comp_apply]
  rw [twoVertexTensorEmbedding_isometry q hq hq1,unitaryQuantumClebschMap_isometry]

end AMSPhysical
#print axioms AMSPhysical.twoRowRootStringEmbedding_mem_channel
#print axioms AMSPhysical.twoRowRootStringEmbedding_isometry

import QuantumMixedFusionComplete
import QuantumMixedFusionWeight
import CompactHighestOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFusionHighestAt_ne_zero (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : MixedFusionIndex l m) : mixedFusionHighestAt q n l m r≠0 := by
  intro hz
  have he := mixedFusionHighestAt_boundary q hq n hn l m r (mixedBoundaryAt n l m r)
  rw [hz,map_zero,Finsupp.zero_apply,if_pos rfl] at he
  norm_num at he

/-- Distinct actual mixed channels are orthogonal in the independently
constructed physical product metric. The whole cyclic modules are covered. -/
theorem mixedFusionChannels_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r s : MixedFusionIndex l m) (hrs : r≠s) :
    mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m s≤
      LinearMap.BilinForm.orthogonal (mixedTensorBilin q n l m)
        (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply compact_highest_cyclic_orthogonal (V:=V) q (ne_of_gt hq) n
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedTensorBilin q n l m) (typeAMixedTensor_compact q hq hq1 n l m)
    (mixedTensorBilin_symm q n l m)
    (mixedFusionHighestAt q n l m r) (mixedFusionHighestAt q n l m s)
    (mixedHighestDynkin n (l-r.val) (m-r.val)) (mixedHighestDynkin n (l-s.val) (m-s.val))
    (mixedFusionHighestAt_E_zero q hq hq1 n l m r)
    (mixedFusionHighestAt_E_zero q hq hq1 n l m s)
    (mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m s)
  let i : Fin n := ⟨0,hn⟩
  apply pairAdjoint_eigen_orthogonal ((typeAMixedTensor_compact q hq hq1 n l m).adjK i)
    (mixedFusionHighestAt q n l m r) (mixedFusionHighestAt q n l m s)
    (q^(mixedHighestDynkin n (l-r.val) (m-r.val) i))
    (q^(mixedHighestDynkin n (l-s.val) (m-s.val) i))
    (mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r i)
    (mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m s i)
  intro he
  apply hrs
  apply mixedFusionHighest_first_weight_injective n hn l m
  exact zpow_right_injective₀ hq hq1 he

end AMSPhysical
#print axioms AMSPhysical.mixedFusionChannels_orthogonal

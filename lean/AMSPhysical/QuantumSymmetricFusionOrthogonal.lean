import QuantumSymmetricFusionComplete
import TwoRowHighestWeight
import CompactHighestOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoRowHighestAt_ne_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) : twoRowHighestAt q n hn l m r≠0 := by
  intro hz
  have he:=twoRowHighestAt_boundary q n hn l m r (twoRowBoundaryAt n hn l m r)
  rw [hz,map_zero,Finsupp.zero_apply,if_pos rfl] at he
  norm_num at he

theorem symmetricFusionChannels_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r s : TwoRowFusionIndex l m) (hrs : r≠s) :
    symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m s≤
      LinearMap.BilinForm.orthogonal (symmetricTensorBilin q n l m)
        (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply compact_highest_cyclic_orthogonal (V:=V) q (ne_of_gt hq) n
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (symmetricTensorBilin q n l m) (typeASymmetricTensor_compact q hq hq1 n l m)
    (symmetricTensorBilin_symm q n l m)
    (twoRowHighestAt q n hn l m r) (twoRowHighestAt q n hn l m s)
    (twoRowHighestWeight n hn l m r.val) (twoRowHighestWeight n hn l m s.val)
    (twoRowHighestAt_E_zero q hq hq1 n hn l m r) (twoRowHighestAt_E_zero q hq hq1 n hn l m s)
    (twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m s)
  let i : Fin n := ⟨0,hn⟩
  apply pairAdjoint_eigen_orthogonal ((typeASymmetricTensor_compact q hq hq1 n l m).adjK i)
    (twoRowHighestAt q n hn l m r) (twoRowHighestAt q n hn l m s)
    (q^(twoRowHighestWeight n hn l m r.val i)) (q^(twoRowHighestWeight n hn l m s.val i))
    (twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r i)
    (twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m s i)
  intro he
  apply hrs
  apply twoRowHighest_first_weight_injective n hn l m
  exact zpow_right_injective₀ hq hq1 he

end AMSPhysical

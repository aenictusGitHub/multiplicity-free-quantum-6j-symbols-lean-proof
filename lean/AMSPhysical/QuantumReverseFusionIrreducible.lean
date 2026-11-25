import QuantumReverseFusion
import IrreducibleTwistedEquivalence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem reverseMixedFusionChannelAt_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m))
    (hSC : S≤reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (hS : algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) S) :
    S=⊥ ∨ S=reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  rw [← reverseMixedFusionChannelAt_map] at hSC ⊢
  exact irreducible_map_of_twisted_equivalence (V:=V) (W:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (typeADynkinReflection q n) (mixedReflection n l m)
    (mixedReflection_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (mixedFusionChannelAt_irreducible q hq hq1 n hn l m r) S hSC hS

end AMSPhysical

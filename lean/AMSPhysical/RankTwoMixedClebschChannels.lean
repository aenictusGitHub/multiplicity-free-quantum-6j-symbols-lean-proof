import RankTwoMixedTensorEquivalence
import RankTwoIntertwinerRange
import QuantumClebschIsometry
import MixedFusionHighestUnique
import QuantumMixedFusionComplete

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def rankTwoMixedClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : MixedFusionIndex l m) :
    finiteWeightSpace (K:=ℝ) (coupledLabel l m r) →ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m :=
  (rankTwoMixedPairEquiv l m).toLinearMap.comp (unitaryQuantumClebschMap q hq hq1 l m r)

theorem rankTwoMixedClebsch_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : MixedFusionIndex l m)
    (z : UqTypeA q 1) (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    rankTwoMixedClebsch q hq hq1 l m r
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (coupledLabel l m r) (rankTwoToSL2 q z) v)=
      typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m z
        (rankTwoMixedClebsch q hq hq1 l m r v) := by
  unfold rankTwoMixedClebsch
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [← unitaryQuantumClebschMap_intertwines q hq hq1 l m r (rankTwoToSL2 q z) v,
    rankTwoMixedPairEquiv_intertwines]

theorem mixedHighestDynkin_rankTwo_coupled (l m : ℕ) (r : MixedFusionIndex l m) (i : Fin 1) :
    mixedHighestDynkin 1 (l-r.val) (m-r.val) i=(coupledLabel l m r:ℤ) := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  have hc : (0:Fin 1).castSucc=(0:Fin 2) := by decide
  have hs : (0:Fin 1).succ=Fin.last 1 := by decide
  simp only [mixedHighestDynkin,if_pos hc,if_pos hs,mul_one]
  unfold coupledLabel
  have hr:=r.isLt
  omega

theorem rankTwoMixedClebsch_highest_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : MixedFusionIndex l m) :
    rankTwoMixedClebsch q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) 0)∈
      mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m r := by
  have he:=mixedFusionHighestAt_full_weight_unique q hq hq1 1 (by omega) l m r
    (rankTwoMixedClebsch q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) 0))
    (by intro i;have hi : i=0 := Subsingleton.elim _ _;subst i
        exact rankTwoIntertwiner_highest_E (W:=quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m) q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          (coupledLabel l m r)
          (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m)
          (rankTwoMixedClebsch q hq hq1 l m r) (rankTwoMixedClebsch_intertwines q hq hq1 l m r))
    (by intro i;rw [mixedHighestDynkin_rankTwo_coupled]
        have hi : i=0 := Subsingleton.elim _ _;subst i
        exact rankTwoIntertwiner_highest_K (W:=quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m) q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          (coupledLabel l m r)
          (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m)
          (rankTwoMixedClebsch q hq hq1 l m r) (rankTwoMixedClebsch_intertwines q hq hq1 l m r))
  rw [he]
  exact Submodule.smul_mem _ _ (algebraCyclicSpan_self _ _)

/-- Every vector of the independently constructed standard Clebsch map
lands in the actual physical mixed channel with the same contraction label. -/
theorem rankTwoMixedClebsch_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : MixedFusionIndex l m)
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    rankTwoMixedClebsch q hq hq1 l m r v∈
      mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m r := by
  let W := quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact rankTwoIntertwiner_range_mem (W:=W) q hq hq1 (coupledLabel l m r)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m)
    (rankTwoMixedClebsch q hq hq1 l m r)
    (rankTwoMixedClebsch_intertwines q hq hq1 l m r)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m r)
    (algebraCyclicSpan_invariant (V:=W)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m)
      (mixedFusionHighestAt q 1 l m r))
    (rankTwoMixedClebsch_highest_channel q hq hq1 l m r) v

end AMSPhysical
#print axioms AMSPhysical.rankTwoMixedClebsch_channel

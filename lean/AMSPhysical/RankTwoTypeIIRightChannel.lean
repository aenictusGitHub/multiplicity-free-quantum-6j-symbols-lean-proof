import RankTwoTypeIITripleEquivalence
import RankTwoMixedClebschChannels
import TensorRightMapRange
import QuantumTypeIIRightChannels
import TypeIIShiftedPaths

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem rankTwoRightTypeIITripleEquiv_Clebsch (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c:ℕ)
    (u:Fin (min b c+1))
    (v:finiteWeightSpace (K:=ℝ) a ⊗[ℝ] finiteWeightSpace (K:=ℝ) (coupledLabel b c u)):
    rankTwoRightTypeIITripleEquiv a b c
      (TensorProduct.map (1:Module.End ℝ (finiteWeightSpace (K:=ℝ) a))
        (unitaryQuantumClebschMap q hq hq1 b c u) v)=
      TensorProduct.map (rankTwoSymmetricEquiv a).toLinearMap
        (rankTwoMixedClebsch q hq hq1 b c u) v := by
  induction v using TensorProduct.induction_on with
  | zero=>simp
  | add v w hv hw=>simp only [map_add,hv,hw]
  | tmul x y=>
    simp only [TensorProduct.map_tmul,LinearMap.id_apply,rankTwoRightTypeIITripleEquiv,
      TensorProduct.congr_tmul,Module.End.one_apply]
    rfl

theorem rankTwoTypeIITripleEquiv_rightTree_channel (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c:ℕ)
    (p:RightHighestPath a b c):
    rankTwoTypeIITripleEquiv a b c (quantumRightTreeHighest q hq hq1 a b c p.1 p.2)∈
      LinearMap.range (TensorProduct.map (LinearMap.id:Module.End ℝ (quantumOccupationSpace ℝ (Fin 2) a))
        (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 b c p.1).subtype) := by
  unfold quantumRightTreeHighest quantumRightTreeMap rankTwoTypeIITripleEquiv
  simp only [LinearMap.comp_apply,LinearEquiv.trans_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  rw [rankTwoRightTypeIITripleEquiv_Clebsch]
  exact tensorRight_map_mem_range (rankTwoSymmetricEquiv a).toLinearMap
    (rankTwoMixedClebsch q hq hq1 b c p.1) _ (rankTwoMixedClebsch_channel q hq hq1 b c p.1) _

def typeIIShiftedRightCupIndex (h a b c:ℕ) (t:QuantumCupIndex a c b):QuantumCupIndex (a+h) c (b+h):=
  ⟨t.val,by have ha:=t.property.1;have hb:=t.property.2;constructor <;> omega⟩

theorem typeIIRightIndex_val (a b c:ℕ) (t:QuantumCupIndex a c b):
    (typeIIRightIndex a b c t).val=c-t.val.val := rfl

theorem rankTwoTypeIITripleEquiv_shiftedRight_channel (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c:ℕ) (t:QuantumCupIndex a c b):
    rankTwoTypeIITripleEquiv (a+h) (b+h) c
      (quantumRightTreeHighest q hq hq1 (a+h) (b+h) c
        (typeIIShiftedRightPath h a b c t).1 (typeIIShiftedRightPath h a b c t).2)∈
      physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (a+h) (b+h) c
        (typeIIShiftedRightCupIndex h a b c t) := by
  have hi:(typeIIShiftedRightPath h a b c t).1=
      typeIIRightIndex (a+h) (b+h) c (typeIIShiftedRightCupIndex h a b c t):=by
    apply Fin.ext
    rfl
  have he:=rankTwoTypeIITripleEquiv_rightTree_channel q hq hq1 (a+h) (b+h) c
    (typeIIShiftedRightPath h a b c t)
  change _∈LinearMap.range (TensorProduct.map _ (mixedFusionChannelAt _ _ _ _ _ _ _).subtype)
  have hch: mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (b+h) c
      (typeIIShiftedRightPath h a b c t).1=
      mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (b+h) c
        (typeIIRightIndex (a+h) (b+h) c (typeIIShiftedRightCupIndex h a b c t)):=
    congrArg (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (b+h) c) hi
  rw [← hch]
  exact he

end AMSPhysical
#print axioms AMSPhysical.rankTwoTypeIITripleEquiv_shiftedRight_channel

import ActualMixedBoundaryCartan
import GlobalSharedRightVertices
import GlobalMixedCommutorBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W Z : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

theorem tensorFirstFunctional_map_right (e : V →ₗ[ℝ] ℝ) (F : W →ₗ[ℝ] Z) (v : V ⊗[ℝ] W) :
    tensorFirstFunctional e (TensorProduct.map LinearMap.id F v)=F (tensorFirstFunctional e v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul v w => simp only [TensorProduct.map_tmul,LinearMap.id_apply,tensorFirstFunctional_tmul,map_smul]

theorem globalSymMixedVertex_raw_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :
    0 < mixedFirstBoundaryFunctional (h+1) p s
      (tensorFirstFunctional (occupationHighestFunctional (h+1) a)
        (TensorProduct.map LinearMap.id
          (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
          (globalSymMixedVertex q hq hq1 h a p s d hbal hs
            (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))))) := by
  have hFactor:=globalTypeIIRightVertex_highest_factor q hq hq1 h a p s d hbal hs 0
  rw [globalMixedPairClebsch_zero] at hFactor
  have he:=congrArg (physicalAllFirstFunctional (h+1) a p s) hFactor
  rw [physicalAllFirstFunctional_mixed] at he
  dsimp only [LinearMap.comp_apply] at he
  have hp:=globalTypeIIRightVector_first_boundary_pos q hq hq1 h a p s d hbal hs 0
  change 0<physicalAllFirstFunctional (h+1) a p s
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs 0).val at hp
  rw [physicalAllFirstFunctional_mixed] at hp
  exact lt_of_lt_of_eq hp he.symm

theorem globalSymMixedVertex_actual_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :
    0 < amsActualBoundary q hq hq1 (h+1) (by omega)
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      ((actualMixedCarrier q hq hq1 (h+1) (by omega) p s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep)
        (tensorFirstFunctional
          ((actualSymmetricCarrier q hq hq1 (h+1) a).frame.pairing
            (actualSymmetricCarrier q hq hq1 (h+1) a).frame.highest)
          (globalSymMixedVertex q hq hq1 h a p s d hbal hs
            (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))))) := by
  have hK:=projected_highest_Cartan q (ne_of_gt hq) (h+1) _ _
    (symmetricHighestRealization q hq hq1 (h+1) a)
    (symmetricHighestRealization q hq hq1 (h+1) d)
    (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).frame.action
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs)
    (globalSymMixedVertex_intertwines q hq hq1 h a p s d hbal hs)
  have hBoundary:=amsActualBoundary_mixed_projected_Cartan q hq hq1 (h+1)
    (show 2≤h+1 from by omega) a p s d hbal _ hK
  refine lt_of_lt_of_eq ?_ hBoundary.symm
  change 0<mixedFirstBoundaryFunctional (h+1) p s
    (tensorFirstFunctional
      ((actualSymmetricCarrier q hq hq1 (h+1) a).frame.pairing
        (actualSymmetricCarrier q hq hq1 (h+1) a).frame.highest)
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))).val
  have he : (actualSymmetricCarrier q hq hq1 (h+1) a).frame.pairing
      (actualSymmetricCarrier q hq hq1 (h+1) a).frame.highest=occupationHighestFunctional (h+1) a := by
    apply LinearMap.ext
    exact symmetric_highest_functional_coordinate q hq (h+1) a
  rw [he]
  have hNatural:=tensorFirstFunctional_map_right (occupationHighestFunctional (h+1) a)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
  have hp:=globalSymMixedVertex_raw_boundary_pos q hq hq1 h a p s d hbal hs
  exact lt_of_lt_of_eq hp (congrArg (mixedFirstBoundaryFunctional (h+1) p s) hNatural)

end AMSPhysical
#print axioms AMSPhysical.globalSymMixedVertex_actual_boundary_pos

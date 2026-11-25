import ActualForwardMixedVertexEntry
import ReverseInnerBoundary
import ReverseInnerHighestLine
import GlobalSharedRightVertices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem globalReverseMixedPairClebsch_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :
    globalReverseMixedPairClebsch q hq hq1 n hn p s r (actualMixedCarrier q hq hq1 n hn p s).frame.highest =
      normalizedReverseMixedFusionHighestAt q n (s+r) (p+r) (globalMixedPairIndex s p r) :=
  (globalMixedPairRealization q hq hq1 n hn p s 0).transport_highest (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r)

theorem actualPositiveVertexTable_reverse_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (p s r : ℕ) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualOppositeCarrier q hq hq1 n (by omega) (s+r)).irrep
      (actualSymmetricCarrier q hq hq1 n (p+r)).irrep
      (actualMixedCarrier q hq hq1 n (by omega) p s).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (actualOppositeCarrier q hq hq1 n (by omega) (s+r))
      (actualSymmetricCarrier q hq hq1 n (p+r))
      (actualMixedCarrier q hq hq1 n (by omega) p s)
      (globalReverseMixedPairClebsch q hq hq1 n (by omega) p s r) := by
  have hHighest:=globalReverseMixedPairClebsch_highest q hq hq1 n (show 0<n from by omega) p s r
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    change Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) (s+r) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (p+r))
      q n (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (s+r) (p+r))
      (mixedHighestDynkin n p s))=1
    have hDim:=reverseMixedHighestSpace_finrank_one q hq hq1 n (by omega) (s+r) (p+r) (globalMixedPairIndex s p r)
    change Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) (s+r) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (p+r))
      q n (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (s+r) (p+r))
      (mixedHighestDynkin n ((p+r)-r) ((s+r)-r)))=1 at hDim
    rw [Nat.add_sub_cancel,Nat.add_sub_cancel] at hDim
    exact hDim
  · apply canonicalizeActualVertex_positive (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualOppositeCarrier q hq hq1 n (by omega) (s+r))
      (actualSymmetricCarrier q hq hq1 n (p+r))
      (actualMixedCarrier q hq hq1 n (by omega) p s)
      (occupationAugmentation n (p+r)) (amsActualBoundary_symmetric q hq hq1 n hn (p+r))
      (globalReverseMixedPairClebsch q hq hq1 n (by omega) p s r)
    · exact globalReverseMixedPairClebsch_intertwines q hq hq1 n (by omega) p s r
    · refine (congrArg (fun v=>LinearMap.BilinForm.tmul
        (occupationOppositeBilin q n (s+r)) (occupationCompactBilin q n (p+r)) v v) hHighest).trans ?_
      rw [← reverseMixedTensorBilin_eq_intrinsic]
      exact normalizedReverseMixedFusionHighestAt_norm_one q hq n (by omega)
        (s+r) (p+r) (globalMixedPairIndex s p r)
    · have he : (actualOppositeCarrier q hq hq1 n (by omega) (s+r)).frame.pairing
          (actualOppositeCarrier q hq hq1 n (by omega) (s+r)).frame.highest =
          occupationCoordinate n (s+r) (lowestOccupation n (s+r)) := by
        apply LinearMap.ext
        exact opposite_highest_functional_coordinate q hq n (s+r)
      rw [he]
      have hBoundary:=congrArg (fun v=>occupationAugmentation n (p+r)
        (tensorFirstFunctional (occupationCoordinate n (s+r) (lowestOccupation n (s+r))) v)) hHighest
      dsimp only at hBoundary
      exact lt_of_lt_of_eq (normalizedReverseMixedHighest_augmentation_pos q hq n (by omega)
        (s+r) (p+r) (globalMixedPairIndex s p r)) hBoundary.symm

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_reverse_entry

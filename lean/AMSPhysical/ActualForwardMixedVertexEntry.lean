import ActualTwoRowVertexEntry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem globalMixedPairClebsch_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :
    globalMixedPairClebsch q hq hq1 n hn p s r (actualMixedCarrier q hq hq1 n hn p s).frame.highest =
      normalizedMixedFusionHighestAt q n (p+r) (s+r) (globalMixedPairIndex p s r) :=
  (globalMixedPairRealization q hq hq1 n hn p s 0).transport_highest (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s r)

theorem actualPositiveVertexTable_forward_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (p s r : ℕ) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualSymmetricCarrier q hq hq1 n (p+r)).irrep
      (actualOppositeCarrier q hq hq1 n (by omega) (s+r)).irrep
      (actualMixedCarrier q hq hq1 n (by omega) p s).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 n (p+r))
      (actualOppositeCarrier q hq hq1 n (by omega) (s+r))
      (actualMixedCarrier q hq hq1 n (by omega) p s)
      (globalMixedPairClebsch q hq hq1 n (by omega) p s r) := by
  have hHighest:=globalMixedPairClebsch_highest q hq hq1 n (show 0<n from by omega) p s r
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    change Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) (p+r) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (s+r))
      q n (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (p+r) (s+r))
      (mixedHighestDynkin n p s))=1
    have hDim:=mixedHighestSpace_finrank_one q hq hq1 n (by omega) (p+r) (s+r) (globalMixedPairIndex p s r)
    change Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) (p+r) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (s+r))
      q n (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (p+r) (s+r))
      (mixedHighestDynkin n ((p+r)-r) ((s+r)-r)))=1 at hDim
    rw [Nat.add_sub_cancel,Nat.add_sub_cancel] at hDim
    exact hDim
  · apply canonicalizeActualVertex_positive (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualSymmetricCarrier q hq hq1 n (p+r))
      (actualOppositeCarrier q hq hq1 n (by omega) (s+r))
      (actualMixedCarrier q hq hq1 n (by omega) p s)
      (occupationAugmentation n (s+r)) (amsActualBoundary_opposite q hq hq1 n hn (s+r))
      (globalMixedPairClebsch q hq hq1 n (by omega) p s r)
    · exact globalMixedPairClebsch_intertwines q hq hq1 n (by omega) p s r
    · refine (congrArg (fun v=>LinearMap.BilinForm.tmul
        (occupationCompactBilin q n (p+r)) (occupationOppositeBilin q n (s+r)) v v) hHighest).trans ?_
      rw [← mixedTensorBilin_eq_intrinsic]
      exact normalizedMixedFusionHighestAt_norm_one q hq n (by omega) (p+r) (s+r) (globalMixedPairIndex p s r)
    · have he : (actualSymmetricCarrier q hq hq1 n (p+r)).frame.pairing
          (actualSymmetricCarrier q hq hq1 n (p+r)).frame.highest =
          occupationCoordinate n (p+r) (highestOccupation n (p+r)) := by
        apply LinearMap.ext
        exact symmetric_highest_functional_coordinate q hq n (p+r)
      rw [he]
      have hBoundary:=congrArg (fun v=>occupationAugmentation n (s+r)
        (tensorFirstFunctional (occupationCoordinate n (p+r) (highestOccupation n (p+r))) v)) hHighest
      dsimp only at hBoundary
      exact lt_of_lt_of_eq (normalizedMixedHighest_augmentation_pos q hq n (by omega)
        (p+r) (s+r) (globalMixedPairIndex p s r)) hBoundary.symm

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_forward_entry

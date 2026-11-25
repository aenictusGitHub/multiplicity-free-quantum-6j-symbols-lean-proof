import ActualAMSBoundary
import ActualCarrierEquivalences
import NativeInnerHighestLines
import OccupationTensorHighestSlices
import TensorWeightedBilinIntrinsic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem globalTwoRowIn_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r : ℕ) (hr : 2*r≤S) (l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m) :
    globalTwoRowIn q hq hq1 n hn S r hr l m hS hl hm
      (actualTwoRowCarrier q hq hq1 n hn S r hr).frame.highest =
        normalizedTwoRowHighest q n hn l m r hl hm :=
  (globalTwoRowCarrier q hq hq1 n hn S r hr).transport_highest (ne_of_gt hq)
    (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)

theorem globalTwoRowIn_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r : ℕ) (hr : 2*r≤S) (l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m)
    (z : UqTypeA q n) (v : (globalTwoRowCarrier q hq hq1 n hn S r hr).channel) :
    globalTwoRowIn q hq hq1 n hn S r hr l m hS hl hm
      ((globalTwoRowCarrier q hq hq1 n hn S r hr).channelAction z v) =
      typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
        (globalTwoRowIn q hq hq1 n hn S r hr l m hS hl hm v) :=
  (globalTwoRowCarrier q hq hq1 n hn S r hr).transport_intertwines (ne_of_gt hq)
    (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm) z v

/-- Concrete identification of the symmetric–symmetric vertex with an
entry of the single table on actual representation weights. -/
theorem actualPositiveVertexTable_twoRow_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (S r : ℕ) (hr : 2*r≤S)
    (l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualSymmetricCarrier q hq hq1 n l).irrep (actualSymmetricCarrier q hq hq1 n m).irrep
      (actualTwoRowCarrier q hq hq1 n (by omega) S r hr).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 n l) (actualSymmetricCarrier q hq hq1 n m)
      (actualTwoRowCarrier q hq hq1 n (by omega) S r hr)
      (globalTwoRowIn q hq hq1 n (by omega) S r hr l m hS hl hm) := by
  have hHighest:=globalTwoRowIn_highest q hq hq1 n (show 0<n from by omega) S r hr l m hS hl hm
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    change Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      q n (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
      (twoRowHighestWeight n (by omega) S 0 r))=1
    rw [← twoRowHighestWeight_total n (by omega) S l m r hS]
    exact twoRowHighestSpace_finrank_one q hq hq1 n (by omega) l m ⟨r,by omega⟩
  · apply canonicalizeActualVertex_positive (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualSymmetricCarrier q hq hq1 n l) (actualSymmetricCarrier q hq hq1 n m)
      (actualTwoRowCarrier q hq hq1 n (by omega) S r hr)
      (occupationAugmentation n m) (amsActualBoundary_symmetric q hq hq1 n hn m)
      (globalTwoRowIn q hq hq1 n (by omega) S r hr l m hS hl hm)
    · intro z v
      change globalTwoRowIn q hq hq1 n (by omega) S r hr l m hS hl hm
        ((globalTwoRowCarrier q hq hq1 n (by omega) S r hr).channelAction z v) =
        typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
          (globalTwoRowIn q hq hq1 n (by omega) S r hr l m hS hl hm v)
      exact globalTwoRowIn_intertwines q hq hq1 n (by omega) S r hr l m hS hl hm z v
    · refine (congrArg (fun v=>LinearMap.BilinForm.tmul
        (occupationCompactBilin q n l) (occupationCompactBilin q n m) v v) hHighest).trans ?_
      rw [← symmetricTensorBilin_eq_intrinsic]
      exact normalizedTwoRowHighest_norm_one q hq hq1 n (by omega) l m r hl hm
    · have he : (actualSymmetricCarrier q hq hq1 n l).frame.pairing
          (actualSymmetricCarrier q hq hq1 n l).frame.highest =
          occupationCoordinate n l (highestOccupation n l) := by
        apply LinearMap.ext
        exact symmetric_highest_functional_coordinate q hq n l
      rw [he]
      have hBoundary:=congrArg (fun v=>occupationAugmentation n m
        (tensorFirstFunctional (occupationCoordinate n l (highestOccupation n l)) v)) hHighest
      dsimp only at hBoundary
      exact lt_of_lt_of_eq (normalizedTwoRowHighest_augmentation_pos q hq n (by omega) l m r hl hm) hBoundary.symm

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_twoRow_entry

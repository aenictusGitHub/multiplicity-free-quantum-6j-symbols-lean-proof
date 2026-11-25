import QuantumSymmetricHighestRealization
import GlobalMixedOrientationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

def oppositeHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    CompactHighestRealization q n (quantumOccupationSpace ℝ (Fin (n+1)) L) (mixedHighestDynkin n 0 L) where
  action := typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L
  pairing := occupationOppositeBilin q n L
  highest := quantumOccupationBasis (K:=ℝ) L (lowestOccupation n L)
  compact := typeAOppositeSymmetric_compact q hq hq1 n L
  symmetric := occupationOppositeBilin_symm q n L
  definite := by
    intro v hv
    exact finiteWeightedPair_definite (occupationOppositeWeight q n L)
      (occupationOppositeWeight_pos q hq n L)
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.injective v hv
  highestE := typeAOpposite_highest_E q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L
  highestK := by
    intro i
    rw [typeAOpposite_generator]
    change typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 3 _ = _
    rw [typeAFiniteGenerator_Ki_basis,simpleOccupationWeight_lowest]
    simp only [mixedHighestDynkin,Nat.cast_zero,zero_mul,zero_add,neg_neg]
    congr 1
    congr 1
    ring
  highestNorm := by
    change finiteWeightedPair (occupationOppositeWeight q n L)
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap _ _ = 1
    rw [finiteWeightedPair_basis,if_pos rfl,occupationOppositeWeight_highest q hq]

theorem oppositeHighestRealization_channel_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    (oppositeHighestRealization q hq hq1 n L).channel=⊤ := by
  let X:=oppositeHighestRealization q hq hq1 n L
  rcases typeAOppositeSymmetric_irreducible q hq hq1 n L X.channel
    (algebraCyclicSpan_invariant X.action X.highest) with he|he
  · have hh : X.highest∈X.channel:=algebraCyclicSpan_self X.action X.highest
    rw [he,Submodule.mem_bot] at hh
    have hn:=X.highestNorm
    rw [hh,map_zero] at hn
    norm_num at hn
  · exact he

end AMSPhysical
#print axioms AMSPhysical.oppositeHighestRealization_channel_top

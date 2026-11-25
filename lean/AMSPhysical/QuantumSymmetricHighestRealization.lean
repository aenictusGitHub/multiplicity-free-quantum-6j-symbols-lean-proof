import CompactHighestRealization
import QuantumTypeAOppositeCompact
import QuantumPureOccupationNorms
import QuantumTripleHighestBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem occupationCompactBilin_definite (q : ℝ) (hq : 0<q) (n L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) (hv : occupationCompactBilin q n L v v=0) : v=0 :=
  finiteWeightedPair_definite (occupationCompactWeight q n L) (occupationCompactWeight_pos q hq n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.injective v hv

def symmetricHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    CompactHighestRealization q n (quantumOccupationSpace ℝ (Fin (n+1)) L) (mixedHighestDynkin n L 0) where
  action := typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L
  pairing := occupationCompactBilin q n L
  highest := quantumOccupationBasis (K:=ℝ) L (highestOccupation n L)
  compact := typeASymmetric_compact q hq hq1 n L
  symmetric := occupationCompactBilin_symm q n L
  definite := occupationCompactBilin_definite q hq n L
  highestE := typeAFiniteGenerator_highest_E q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L
  highestK := by
    intro i
    change typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2 _=_
    rw [typeAFiniteGenerator_K_basis,simpleOccupationWeight_highest]
    simp only [mixedHighestDynkin,Nat.cast_zero,zero_mul,add_zero]
  highestNorm := by
    change finiteWeightedPair (occupationCompactWeight q n L)
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
      (quantumOccupationBasis (K:=ℝ) L (highestOccupation n L))
      (quantumOccupationBasis (K:=ℝ) L (highestOccupation n L))=1
    rw [finiteWeightedPair_basis,if_pos rfl,occupationCompactWeight_highest q hq]

theorem symmetricHighestRealization_channel_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    (symmetricHighestRealization q hq hq1 n L).channel=⊤ := by
  apply typeAInvariant_cyclic_highest q hq hq1 n L
  · exact algebraCyclicSpan_invariant _ _
  · exact algebraCyclicSpan_self _ _

end AMSPhysical

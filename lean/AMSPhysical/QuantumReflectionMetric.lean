import QuantumOccupationReflection
import QuantumTypeAOppositeCompact
import QuantumTypeACompact
import WeightedBasisEquivalence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem occupationReflection_opposite_weight (q : ℝ) (hq : q≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) :
    occupationOppositeWeight q n L (occupationReflection n L x)=occupationCompactWeight q n L x := by
  have h:=occupationReflection_compact_weight q hq n L (occupationReflection n L x)
  rw [occupationReflection_involutive] at h
  exact h.symm

theorem quantumOccupationReflection_compact_isometry (q : ℝ) (hq : q≠0) (n L : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationOppositeBilin q n L (quantumOccupationReflection n L v) (quantumOccupationReflection n L w)=
      occupationCompactBilin q n L v w := by
  apply weightedBasisEquiv_isometry
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L) (occupationReflectionEquiv n L)
    (occupationCompactWeight q n L) (occupationOppositeWeight q n L) _ v w
  exact occupationReflection_opposite_weight q hq n L

theorem quantumOccupationReflection_opposite_isometry (q : ℝ) (hq : q≠0) (n L : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationCompactBilin q n L (quantumOccupationReflection n L v) (quantumOccupationReflection n L w)=
      occupationOppositeBilin q n L v w := by
  apply weightedBasisEquiv_isometry
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L) (occupationReflectionEquiv n L)
    (occupationOppositeWeight q n L) (occupationCompactWeight q n L) _ v w
  exact occupationReflection_compact_weight q hq n L

end AMSPhysical

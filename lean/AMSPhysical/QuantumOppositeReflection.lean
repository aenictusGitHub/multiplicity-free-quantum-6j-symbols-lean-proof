import QuantumReflectionIntertwiner
import QuantumDynkinChevalley

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem quantumOccupationReflection_opposite_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) (z : UqTypeA q n) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    quantumOccupationReflection n L (typeAOppositeSymmetricRepresentation q hq hD n L z v)=
      typeAFiniteQuantumRepresentation q hq hD n L (typeADynkinReflection q n z)
        (quantumOccupationReflection n L v) := by
  have hc := congrArg (fun f =>f z) (typeADynkinReflection_chevalley q hq n)
  change typeADynkinReflection q n (typeAChevalley q hq n z)=
    typeAChevalley q hq n (typeADynkinReflection q n z) at hc
  change quantumOccupationReflection n L
      (typeAFiniteQuantumRepresentation q hq hD n L (typeAChevalley q hq n z) v)=_
  rw [quantumOccupationReflection_intertwines,hc]
  change typeAFiniteQuantumRepresentation q hq hD n L
    (typeAChevalley q hq n (typeAChevalley q hq n (typeADynkinReflection q n z)))
      (quantumOccupationReflection n L v)=_
  rw [typeAChevalley_involutive]

end AMSPhysical

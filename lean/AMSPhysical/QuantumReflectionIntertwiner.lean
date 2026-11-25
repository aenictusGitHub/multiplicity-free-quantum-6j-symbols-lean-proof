import QuantumReflectionCartan
import QuantumTypeADynkinReflection
import QuantumTypeAIntertwiner
import QuantumTypeADualSymmetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem quantumOccupationReflection_generator_coe (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) (i : Fin n) (t : Fin 4) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    (quantumOccupationReflection n L (typeAFiniteGenerator q hq hD n L i t v)).val=
      ![typeAQuantumF q n i.rev,typeAQuantumE q n i.rev,typeAQuantumKi q n i.rev,typeAQuantumK q n i.rev] t
        (quantumOccupationReflection n L v).val := by
  rw [quantumOccupationReflection_coe,typeAFiniteGenerator_coe,quantumOccupationReflection_coe]
  fin_cases t
  · exact quantumLatticeReflection_typeA_E q n i v.val
  · exact quantumLatticeReflection_typeA_F q n i v.val
  · exact quantumLatticeReflection_typeA_K q n i v.val
  · exact quantumLatticeReflection_typeA_Ki q n i v.val

/-- Exact physical coordinate reversal realizes the Dynkin reflection between
the actual symmetric module and its Chevalley-twisted opposite. -/
theorem quantumOccupationReflection_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) (z : UqTypeA q n) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    quantumOccupationReflection n L (typeAFiniteQuantumRepresentation q hq hD n L z v)=
      typeAOppositeSymmetricRepresentation q hq hD n L (typeADynkinReflection q n z)
        (quantumOccupationReflection n L v) := by
  apply typeA_intertwiner_of_generators q n
    (typeAFiniteQuantumRepresentation q hq hD n L)
    ((typeAOppositeSymmetricRepresentation q hq hD n L).comp (typeADynkinReflection q n))
    (quantumOccupationReflection n L).toLinearMap _ z v
  intro i t x
  simp only [AlgHom.comp_apply,typeADynkinReflection_generator]
  apply Subtype.ext
  change (quantumOccupationReflection n L (typeAFiniteGenerator q hq hD n L i t x)).val=_
  rw [quantumOccupationReflection_generator_coe,typeAOpposite_generator]
  fin_cases t
  · exact (typeAFiniteGenerator_coe q hq hD n L i.rev 1 (quantumOccupationReflection n L x)).symm
  · exact (typeAFiniteGenerator_coe q hq hD n L i.rev 0 (quantumOccupationReflection n L x)).symm
  · exact (typeAFiniteGenerator_coe q hq hD n L i.rev 3 (quantumOccupationReflection n L x)).symm
  · exact (typeAFiniteGenerator_coe q hq hD n L i.rev 2 (quantumOccupationReflection n L x)).symm

end AMSPhysical
#print axioms AMSPhysical.quantumOccupationReflection_intertwines

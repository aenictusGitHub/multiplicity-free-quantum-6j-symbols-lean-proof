import QuantumTypeAAlgebra
import QuantumOccupation
import PreservingEndAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def typeAOccupationGenerator (q : K) (n L : ℕ) (i : Fin n) (t : Fin 4) :
    preservingEndAlgebra (quantumOccupationSpace K (Fin (n+1)) L) :=
  ![⟨typeAQuantumE q n i,quantumLatticeMove_preserves q L i.castSucc i.succ (typeA_root_endpoints n i)⟩,
    ⟨typeAQuantumF q n i,quantumLatticeMove_preserves q L i.succ i.castSucc (Ne.symm (typeA_root_endpoints n i))⟩,
    ⟨typeAQuantumK q n i,quantumLatticeCartan_preserves q L (typeARoot n i)⟩,
    ⟨typeAQuantumKi q n i,quantumLatticeCartan_preserves q L (-typeARoot n i)⟩] t

@[simp] theorem typeAOccupationGenerator_coe (q : K) (n L : ℕ) (i : Fin n) (t : Fin 4) :
    (typeAOccupationGenerator q n L i t : Module.End K (QuantumLatticeSpace K (Fin (n+1))))=
      ![typeAQuantumE q n i,typeAQuantumF q n i,typeAQuantumK q n i,typeAQuantumKi q n i] t := by
  fin_cases t <;> rfl

def typeAFreeOccupationRepresentation (q : K) (n L : ℕ) :
    FreeAlgebra K (Fin n×Fin 4) →ₐ[K] preservingEndAlgebra (quantumOccupationSpace K (Fin (n+1)) L) :=
  FreeAlgebra.lift K (fun it => typeAOccupationGenerator q n L it.1 it.2)

theorem typeAFreeOccupationRepresentation_coe (q : K) (n L : ℕ) (x : FreeAlgebra K (Fin n×Fin 4)) :
    (typeAFreeOccupationRepresentation q n L x : Module.End K (QuantumLatticeSpace K (Fin (n+1))))=
      typeAFreeRepresentation q n x := by
  have hh : (preservingEndAlgebra (quantumOccupationSpace K (Fin (n+1)) L)).val.comp
      (typeAFreeOccupationRepresentation q n L)=typeAFreeRepresentation q n := by
    apply FreeAlgebra.hom_ext
    funext it
    simp [typeAFreeOccupationRepresentation,typeAFreeRepresentation]
  exact congrArg (fun f => f x) hh

theorem typeAFreeOccupationRepresentation_respects (q : K) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) {x y : FreeAlgebra K (Fin n×Fin 4)} (h : QuantumTypeARelation q n x y) :
    typeAFreeOccupationRepresentation q n L x=typeAFreeOccupationRepresentation q n L y := by
  apply Subtype.ext
  rw [typeAFreeOccupationRepresentation_coe,typeAFreeOccupationRepresentation_coe]
  exact typeAFreeRepresentation_respects q hq hD n h

def typeAPreservingOccupationRepresentation (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) :
    UqTypeA q n →ₐ[K] preservingEndAlgebra (quantumOccupationSpace K (Fin (n+1)) L) :=
  RingQuot.liftAlgHom K ⟨typeAFreeOccupationRepresentation q n L,by
    intro x y h
    exact typeAFreeOccupationRepresentation_respects q hq hD n L h⟩

/-- An actual finite-dimensional fixed-degree representation of the complete
presented Uq(sl_(n+1)), constructed by restriction of all root and torus actions. -/
def typeAFiniteQuantumRepresentation (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) :
    UqTypeA q n →ₐ[K] Module.End K (quantumOccupationSpace K (Fin (n+1)) L) :=
  (restrictPreservingEnd (quantumOccupationSpace K (Fin (n+1)) L)).comp
    (typeAPreservingOccupationRepresentation q hq hD n L)

theorem typeAFiniteQuantumRepresentation_generator_coe (q : K) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n L : ℕ) (i : Fin n) (t : Fin 4) (v : quantumOccupationSpace K (Fin (n+1)) L) :
    (typeAFiniteQuantumRepresentation q hq hD n L
      (RingQuot.mkAlgHom K (QuantumTypeARelation q n) (typeAFreeGenerator n i t)) v).val=
      ![typeAQuantumE q n i,typeAQuantumF q n i,typeAQuantumK q n i,typeAQuantumKi q n i] t v.val := by
  simp [typeAFiniteQuantumRepresentation,typeAPreservingOccupationRepresentation,
    typeAFreeOccupationRepresentation,typeAFreeGenerator,restrictPreservingEnd_apply]

end AMSPhysical

#print axioms AMSPhysical.typeAFiniteQuantumRepresentation
#print axioms AMSPhysical.typeAFiniteQuantumRepresentation_generator_coe

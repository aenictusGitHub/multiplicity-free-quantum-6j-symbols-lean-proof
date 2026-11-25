import QuantumTypeACoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

def typeACounitFree (n : ℕ) : FreeAlgebra K (Fin n×Fin 4) →ₐ[K] K :=
  FreeAlgebra.lift K (fun it => ![(0:K),0,1,1] it.2)

theorem typeACounitFree_respects (q : K) (n : ℕ)
    {x y : FreeAlgebra K (Fin n×Fin 4)} (h : QuantumTypeARelation q n x y) :
    typeACounitFree (K:=K) n x=typeACounitFree (K:=K) n y := by
  cases h <;> simp [typeACounitFree,typeAFreeGenerator]

/-- The ordinary counit of the independently presented quantum algebra. -/
def typeAQuantumCounit (q : K) (n : ℕ) : UqTypeA q n →ₐ[K] K :=
  RingQuot.liftAlgHom K ⟨typeACounitFree (K:=K) n,by intro x y h;exact typeACounitFree_respects q n h⟩

theorem typeAQuantumCounit_generator (q : K) (n : ℕ) (i : Fin n) (t : Fin 4) :
    typeAQuantumCounit q n (typeAAlgebraGenerator q n i t)=![(0:K),0,1,1] t := by
  simp [typeAAlgebraGenerator,typeAQuantumCounit,typeACounitFree,typeAFreeGenerator]

end AMSPhysical
#print axioms AMSPhysical.typeAQuantumCounit

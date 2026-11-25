import QuantumTypeACoproductDistant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {K : Type*} [Field K]

def typeACoproductFree (q : K) (n : ℕ) :
    FreeAlgebra K (Fin n×Fin 4) →ₐ[K] (UqTypeA q n ⊗[K] UqTypeA q n) :=
  FreeAlgebra.lift K (fun it => ![typeACoproductE q n it.1,typeACoproductF q n it.1,
    typeACoproductK q n it.1,typeACoproductKi q n it.1] it.2)

theorem typeACoproductFree_respects (q : K) (hq : q≠0) (n : ℕ)
    {x y : FreeAlgebra K (Fin n×Fin 4)} (h : QuantumTypeARelation q n x y) :
    typeACoproductFree q n x=typeACoproductFree q n y := by
  cases h with
  | inverse i => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_inverse q n i
  | inverse' i => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_inverse' q n i
  | torus i j => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_torus q n i j
  | weightE i j => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_weightE q n i j
  | weightF i j => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_weightF q n i j
  | commutator i => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_commutator q hq n i
  | differentEF i j hij => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_differentEF q hq n i j hij
  | distantE i j hd => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_distantE q n i j hd
  | distantF i j hd => simpa [typeACoproductFree,typeAFreeGenerator] using typeACoproduct_distantF q n i j hd
  | serreELeft i j hij => simpa [typeACoproductFree,typeAFreeGenerator,serrePolynomial] using typeACoproduct_serreELeft q hq n i j hij
  | serreERight i j hij => simpa [typeACoproductFree,typeAFreeGenerator,serrePolynomial] using typeACoproduct_serreERight q hq n i j hij
  | serreFLeft i j hij => simpa [typeACoproductFree,typeAFreeGenerator,serrePolynomial] using typeACoproduct_serreFLeft q hq n i j hij
  | serreFRight i j hij => simpa [typeACoproductFree,typeAFreeGenerator,serrePolynomial] using typeACoproduct_serreFRight q hq n i j hij

/-- The standard coproduct on the complete independently presented Uq(sl_(n+1)). -/
def typeAQuantumCoproduct (q : K) (hq : q≠0) (n : ℕ) :
    UqTypeA q n →ₐ[K] (UqTypeA q n ⊗[K] UqTypeA q n) :=
  RingQuot.liftAlgHom K ⟨typeACoproductFree q n,by intro x y h;exact typeACoproductFree_respects q hq n h⟩

theorem typeAQuantumCoproduct_generator (q : K) (hq : q≠0) (n : ℕ) (i : Fin n) (t : Fin 4) :
    typeAQuantumCoproduct q hq n (typeAAlgebraGenerator q n i t)=
      ![typeACoproductE q n i,typeACoproductF q n i,typeACoproductK q n i,typeACoproductKi q n i] t := by
  simp [typeAAlgebraGenerator,typeAQuantumCoproduct,typeACoproductFree,typeAFreeGenerator]

end AMSPhysical
#print axioms AMSPhysical.typeAQuantumCoproduct

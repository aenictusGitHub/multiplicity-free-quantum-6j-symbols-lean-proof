import QuantumTypeARelations
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]
local notation "U" => typeAAlgebraGenerator

theorem typeACartan_rev (n : ℕ) (i j : Fin n) : typeACartan n i.rev j.rev=typeACartan n i j := by
  unfold typeACartan
  simp only [Fin.rev_injective.eq_iff,Fin.val_rev]
  split_ifs <;> omega

theorem typeADistant_rev (n : ℕ) (i j : Fin n) (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    i.rev.val+1 < j.rev.val ∨ j.rev.val+1 < i.rev.val := by
  simp only [Fin.val_rev]
  omega

theorem typeAAdjacent_rev (n : ℕ) (i j : Fin n) (h : i.val+1=j.val) : j.rev.val+1=i.rev.val := by
  simp only [Fin.val_rev]
  omega

def typeADynkinFree (q : K) (n : ℕ) : FreeAlgebra K (Fin n×Fin 4) →ₐ[K] UqTypeA q n :=
  FreeAlgebra.lift K (fun it =>U q n it.1.rev it.2)

theorem typeADynkinFree_respects (q : K) (n : ℕ)
    {x y : FreeAlgebra K (Fin n×Fin 4)} (h : QuantumTypeARelation q n x y) :
    typeADynkinFree q n x=typeADynkinFree q n y := by
  cases h with
  | inverse i => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_inverse q n i.rev
  | inverse' i => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_inverse' q n i.rev
  | torus i j => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_torus q n i.rev j.rev
  | weightE i j => simpa [typeADynkinFree,typeAFreeGenerator,typeACartan_rev] using uqA_weightE q n i.rev j.rev
  | weightF i j => simpa [typeADynkinFree,typeAFreeGenerator,typeACartan_rev] using uqA_weightF q n i.rev j.rev
  | commutator i => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_commutator q n i.rev
  | differentEF i j hij =>
    simpa [typeADynkinFree,typeAFreeGenerator] using uqA_differentEF q n i.rev j.rev (fun h =>hij (Fin.rev_injective h))
  | distantE i j hd => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_distantE q n i.rev j.rev (typeADistant_rev n i j hd)
  | distantF i j hd => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_distantF q n i.rev j.rev (typeADistant_rev n i j hd)
  | serreELeft i j hij => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_serreERight q n j.rev i.rev (typeAAdjacent_rev n i j hij)
  | serreERight i j hij => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_serreELeft q n j.rev i.rev (typeAAdjacent_rev n i j hij)
  | serreFLeft i j hij => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_serreFRight q n j.rev i.rev (typeAAdjacent_rev n i j hij)
  | serreFRight i j hij => simpa [typeADynkinFree,typeAFreeGenerator] using uqA_serreFLeft q n j.rev i.rev (typeAAdjacent_rev n i j hij)

/-- The actual Dynkin-diagram reflection of the full quantum presentation. -/
def typeADynkinReflection (q : K) (n : ℕ) : UqTypeA q n →ₐ[K] UqTypeA q n :=
  RingQuot.liftAlgHom K ⟨typeADynkinFree q n,by intro x y h;exact typeADynkinFree_respects q n h⟩

theorem typeADynkinReflection_generator (q : K) (n : ℕ) (i : Fin n) (t : Fin 4) :
    typeADynkinReflection q n (U q n i t)=U q n i.rev t := by
  simp [typeADynkinReflection,typeADynkinFree,typeAAlgebraGenerator,typeAFreeGenerator]

theorem typeADynkinReflection_comp_self (q : K) (n : ℕ) :
    (typeADynkinReflection q n).comp (typeADynkinReflection q n)=AlgHom.id K (UqTypeA q n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change typeADynkinReflection q n (typeADynkinReflection q n (U q n i t))=U q n i t
  rw [typeADynkinReflection_generator,typeADynkinReflection_generator,Fin.rev_rev]

theorem typeADynkinReflection_involutive (q : K) (n : ℕ) :
    Function.Involutive (typeADynkinReflection q n) := by
  intro z
  exact congrArg (fun f =>f z) (typeADynkinReflection_comp_self q n)

end AMSPhysical
#print axioms AMSPhysical.typeADynkinReflection_involutive

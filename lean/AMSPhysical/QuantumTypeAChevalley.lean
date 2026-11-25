import QuantumTypeAInverseWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]
local notation "U" => typeAAlgebraGenerator

def typeAChevalleyFree (q : K) (n : ℕ) : FreeAlgebra K (Fin n×Fin 4) →ₐ[K] UqTypeA q n :=
  FreeAlgebra.lift K (fun it => ![U q n it.1 1,U q n it.1 0,U q n it.1 3,U q n it.1 2] it.2)

theorem typeAChevalleyFree_respects (q : K) (hq : q≠0) (n : ℕ)
    {x y : FreeAlgebra K (Fin n×Fin 4)} (h : QuantumTypeARelation q n x y) :
    typeAChevalleyFree q n x=typeAChevalleyFree q n y := by
  cases h with
  | inverse i => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_inverse' q n i
  | inverse' i => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_inverse q n i
  | torus i j => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_torus_inverses q n i j
  | weightE i j => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_Kinv_F q hq n i j
  | weightF i j => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_Kinv_E q hq n i j
  | commutator i =>
    simp only [typeAChevalleyFree,typeAFreeGenerator,map_sub,map_mul,map_smul,FreeAlgebra.lift_ι_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    change U q n i 1*U q n i 0-U q n i 0*U q n i 1=(q-q⁻¹)⁻¹ • (U q n i 3-U q n i 2)
    have hh := uqA_commutator q n i
    calc
      _ = -(U q n i 0*U q n i 1-U q n i 1*U q n i 0) := by abel
      _ = -((q-q⁻¹)⁻¹ • (U q n i 2-U q n i 3)) := congrArg Neg.neg hh
      _ = _ := by simp only [smul_sub];abel
  | differentEF i j hij =>
    simpa [typeAChevalleyFree,typeAFreeGenerator] using (uqA_differentEF q n j i (Ne.symm hij)).symm
  | distantE i j hd => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_distantF q n i j hd
  | distantF i j hd => simpa [typeAChevalleyFree,typeAFreeGenerator] using uqA_distantE q n i j hd
  | serreELeft i j hij => simpa [typeAChevalleyFree,typeAFreeGenerator,serrePolynomial] using uqA_serreFLeft q n i j hij
  | serreERight i j hij => simpa [typeAChevalleyFree,typeAFreeGenerator,serrePolynomial] using uqA_serreFRight q n i j hij
  | serreFLeft i j hij => simpa [typeAChevalleyFree,typeAFreeGenerator,serrePolynomial] using uqA_serreELeft q n i j hij
  | serreFRight i j hij => simpa [typeAChevalleyFree,typeAFreeGenerator,serrePolynomial] using uqA_serreERight q n i j hij

/-- The Chevalley involution of the complete presented type-A quantum algebra. -/
def typeAChevalley (q : K) (hq : q≠0) (n : ℕ) : UqTypeA q n →ₐ[K] UqTypeA q n :=
  RingQuot.liftAlgHom K ⟨typeAChevalleyFree q n,by intro x y h;exact typeAChevalleyFree_respects q hq n h⟩

theorem typeAChevalley_generator (q : K) (hq : q≠0) (n : ℕ) (i : Fin n) (t : Fin 4) :
    typeAChevalley q hq n (U q n i t)=![U q n i 1,U q n i 0,U q n i 3,U q n i 2] t := by
  simp [typeAAlgebraGenerator,typeAChevalley,typeAChevalleyFree,typeAFreeGenerator]

theorem typeAChevalley_comp_self (q : K) (hq : q≠0) (n : ℕ) :
    (typeAChevalley q hq n).comp (typeAChevalley q hq n)=AlgHom.id K (UqTypeA q n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change typeAChevalley q hq n (typeAChevalley q hq n (U q n i t))=U q n i t
  fin_cases t <;> simp [typeAChevalley_generator]

theorem typeAChevalley_involutive (q : K) (hq : q≠0) (n : ℕ) :
    Function.Involutive (typeAChevalley q hq n) := by
  intro x
  exact congrArg (fun f => f x) (typeAChevalley_comp_self q hq n)

theorem typeAChevalley_surjective (q : K) (hq : q≠0) (n : ℕ) :
    Function.Surjective (typeAChevalley q hq n) := (typeAChevalley_involutive q hq n).surjective

end AMSPhysical
#print axioms AMSPhysical.typeAChevalley_involutive

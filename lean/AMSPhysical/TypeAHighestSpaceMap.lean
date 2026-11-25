import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem typeAHighestSpace_map_mem (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (T : V →ₗ[ℝ] W) (hT : ∀ z v,T (ρ z v)=σ z (T v))
    (lam : Fin n → ℤ) (v : V) (hv:v∈typeAHighestSpace q n ρ lam) :
    T v∈typeAHighestSpace q n σ lam := by
  obtain ⟨hE,hK⟩:=(mem_typeAHighestSpace q n ρ lam v).mp hv
  apply (mem_typeAHighestSpace q n σ lam (T v)).mpr
  constructor
  · intro i
    rw [← hT,hE,map_zero]
  · intro i
    rw [← hT,hK,map_smul]

def typeAHighestSpaceMap (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (T : V →ₗ[ℝ] W) (hT : ∀ z v,T (ρ z v)=σ z (T v)) (lam : Fin n → ℤ) :
    typeAHighestSpace q n ρ lam →ₗ[ℝ] typeAHighestSpace q n σ lam :=
  (T.comp (typeAHighestSpace q n ρ lam).subtype).codRestrict _
    (fun v =>typeAHighestSpace_map_mem q n ρ σ T hT lam v.val v.property)

end AMSPhysical
#print axioms AMSPhysical.typeAHighestSpaceMap

import QuantumTypeABending

set_option autoImplicit false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X D B C W : Type*}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup D] [Module ℝ D]
  [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
  [AddCommGroup W] [Module ℝ W]

/-- Bending a pair map that factors through one internal carrier gives the
literal composition of two trivalent vertices, with no extra scalar. -/
theorem bendRight_postcompose (F : C →ₗ[ℝ] W) (T : (X ⊗[ℝ] D) →ₗ[ℝ] C)
    (cup : D ⊗[ℝ] B) :
    bendRight (F.comp T) cup =
      (TensorProduct.map F (LinearMap.id : B →ₗ[ℝ] B)).comp (bendRight T cup) := by
  apply LinearMap.ext
  intro x
  have hm : ∀ z : (X ⊗[ℝ] D) ⊗[ℝ] B,
      TensorProduct.map (F.comp T) (LinearMap.id : B →ₗ[ℝ] B) z =
        TensorProduct.map F LinearMap.id (TensorProduct.map T LinearMap.id z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul u v => rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  exact hm _

end AMSPhysical
#print axioms AMSPhysical.bendRight_postcompose

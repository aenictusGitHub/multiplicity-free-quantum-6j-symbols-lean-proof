import QuantumTypeABending

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W X₂ V₂ W₂ : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup X₂] [Module ℝ X₂] [AddCommGroup V₂] [Module ℝ V₂]
  [AddCommGroup W₂] [Module ℝ W₂]

def rightBendingInCup (T : X ⊗[ℝ] V →ₗ[ℝ] W) (x : X) : V ⊗[ℝ] V →ₗ[ℝ] W ⊗[ℝ] V :=
  (TensorProduct.map T (LinearMap.id : Module.End ℝ V)).comp
    ((TensorProduct.assoc ℝ X V V).symm.toLinearMap.comp (TensorProduct.mk ℝ X (V ⊗[ℝ] V) x))

theorem rightBendingInCup_tmul (T : X ⊗[ℝ] V →ₗ[ℝ] W) (x : X) (u v : V) :
    rightBendingInCup T x (u ⊗ₜ[ℝ] v)=T (x ⊗ₜ[ℝ] u) ⊗ₜ[ℝ] v := by
  simp only [rightBendingInCup,LinearMap.comp_apply,LinearEquiv.coe_coe,TensorProduct.mk_apply,
    TensorProduct.assoc_symm_tmul,TensorProduct.map_tmul,LinearMap.id_apply]

theorem rightBendingInCup_eq_bend (T : X ⊗[ℝ] V →ₗ[ℝ] W) (x : X) (cup : V ⊗[ℝ] V) :
    rightBendingInCup T x cup=bendRight T cup x := by rfl

/-- Literal finite-dimensional naturality of physical bending under full
pair projection and the two-leg cup projection. -/
theorem bendRight_projection_naturality
    (T : X ⊗[ℝ] V →ₗ[ℝ] W) (T₂ : X₂ ⊗[ℝ] V₂ →ₗ[ℝ] W₂)
    (A : X₂ →ₗ[ℝ] X) (P : X →ₗ[ℝ] X₂) (U : V →ₗ[ℝ] V₂) (B : W →ₗ[ℝ] W₂)
    (hPA : ∀ x,P (A x)=x)
    (hPair : ∀ v,B (T v)=T₂ (TensorProduct.map P U v))
    (cup : V ⊗[ℝ] V) (cup₂ : V₂ ⊗[ℝ] V₂)
    (hCup : TensorProduct.map U U cup=cup₂) (x : X₂) :
    TensorProduct.map B U (bendRight T cup (A x))=bendRight T₂ cup₂ x := by
  have he : (TensorProduct.map B U).comp (rightBendingInCup T (A x))=
      (rightBendingInCup T₂ x).comp (TensorProduct.map U U) := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.comp_apply,rightBendingInCup_tmul,TensorProduct.map_tmul,hPair,hPA]
  have hh:=DFunLike.congr_fun he cup
  simpa only [LinearMap.comp_apply,rightBendingInCup_eq_bend,hCup] using hh

end AMSPhysical
#print axioms AMSPhysical.bendRight_projection_naturality

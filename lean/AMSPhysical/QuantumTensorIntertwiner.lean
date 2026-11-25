import QuantumIntertwiner
import TensorQuantumCompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {V W V' W' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem quantumIntertwiner_tensor (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (ρ' : UqSL2 q →ₐ[ℝ] Module.End ℝ V') (σ' : UqSL2 q →ₐ[ℝ] Module.End ℝ W')
    (T : V →ₗ[ℝ] V') (S : W →ₗ[ℝ] W')
    (hT : IsQuantumIntertwiner q ρ ρ' T) (hS : IsQuantumIntertwiner q σ σ' S) :
    IsQuantumIntertwiner (V:=V ⊗[ℝ] W) (W:=V' ⊗[ℝ] W') q
      (tensorRepresentation q hq ρ σ) (tensorRepresentation q hq ρ' σ') (TensorProduct.map T S) := by
  apply quantumIntertwiner_of_generators
  intro i v
  have he : (tensorRepresentation q hq ρ' σ' (uqGenerator q i)).comp (TensorProduct.map T S)=
      (TensorProduct.map T S).comp (tensorRepresentation q hq ρ σ (uqGenerator q i)) := by
    apply TensorProduct.ext'
    intro p w
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul]
    fin_cases i
    · change tensorRepresentation q hq ρ' σ' (uqGenerator q 0) (T p ⊗ₜ[ℝ] S w)=
        TensorProduct.map T S (tensorRepresentation q hq ρ σ (uqGenerator q 0) (p ⊗ₜ[ℝ] w))
      rw [tensorRepresentation_E (V:=V') (W:=W') q hq ρ' σ' (T p) (S w),
        tensorRepresentation_E (V:=V) (W:=W) q hq ρ σ p w,map_add,TensorProduct.map_tmul,TensorProduct.map_tmul,
        hT (uqGenerator q 0) p,hS (uqGenerator q 2) w,hS (uqGenerator q 0) w]
    · change tensorRepresentation q hq ρ' σ' (uqGenerator q 1) (T p ⊗ₜ[ℝ] S w)=
        TensorProduct.map T S (tensorRepresentation q hq ρ σ (uqGenerator q 1) (p ⊗ₜ[ℝ] w))
      rw [tensorRepresentation_F (V:=V') (W:=W') q hq ρ' σ' (T p) (S w),
        tensorRepresentation_F (V:=V) (W:=W) q hq ρ σ p w,map_add,TensorProduct.map_tmul,TensorProduct.map_tmul,
        hT (uqGenerator q 1) p,hT (uqGenerator q 3) p,hS (uqGenerator q 1) w]
    · change tensorRepresentation q hq ρ' σ' (uqGenerator q 2) (T p ⊗ₜ[ℝ] S w)=
        TensorProduct.map T S (tensorRepresentation q hq ρ σ (uqGenerator q 2) (p ⊗ₜ[ℝ] w))
      rw [tensorRepresentation_K (V:=V') (W:=W') q hq ρ' σ' (T p) (S w),
        tensorRepresentation_K (V:=V) (W:=W) q hq ρ σ p w,hT (uqGenerator q 2) p,hS (uqGenerator q 2) w,TensorProduct.map_tmul]
    · change tensorRepresentation q hq ρ' σ' (uqGenerator q 3) (T p ⊗ₜ[ℝ] S w)=
        TensorProduct.map T S (tensorRepresentation q hq ρ σ (uqGenerator q 3) (p ⊗ₜ[ℝ] w))
      rw [tensorRepresentation_Ki_end (V:=V') (W:=W') q hq ρ' σ',
        tensorRepresentation_Ki_end (V:=V) (W:=W) q hq ρ σ,TensorProduct.map_tmul,TensorProduct.map_tmul,
        TensorProduct.map_tmul,hT (uqGenerator q 3) p,hS (uqGenerator q 3) w]
  exact DFunLike.congr_fun he v

theorem quantumIntertwiner_comp {U : Type*} [AddCommGroup U] [Module ℝ U]
    (q : ℝ) (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (τ : UqSL2 q →ₐ[ℝ] Module.End ℝ U) (T : V →ₗ[ℝ] W) (S : W →ₗ[ℝ] U)
    (hT : IsQuantumIntertwiner q ρ σ T) (hS : IsQuantumIntertwiner q σ τ S) :
    IsQuantumIntertwiner q ρ τ (S.comp T) := by
  intro x v
  change τ x (S (T v))=S (T (ρ x v))
  rw [hS x (T v),hT x v]

theorem quantumIntertwiner_inverse (q : ℝ)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (T : V ≃ₗ[ℝ] W) (hT : IsQuantumIntertwiner q ρ σ T.toLinearMap) :
    IsQuantumIntertwiner q σ ρ T.symm.toLinearMap := by
  intro x v
  apply T.injective
  have h := hT x (T.symm v)
  change σ x (T (T.symm v))=T (ρ x (T.symm v)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change T (ρ x (T.symm v))=T (T.symm (σ x v))
  rw [LinearEquiv.apply_symm_apply]
  exact h.symm

end AMSPhysical

#print axioms AMSPhysical.quantumIntertwiner_tensor

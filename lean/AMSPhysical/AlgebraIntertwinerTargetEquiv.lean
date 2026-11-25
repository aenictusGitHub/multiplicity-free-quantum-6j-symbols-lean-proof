import AlgebraIntertwinerSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {A V W Z : Type*} [Ring A] [Algebra ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

theorem algebraIntertwinerEquiv_inverse (σ : A →ₐ[ℝ] Module.End ℝ W) (τ : A →ₐ[ℝ] Module.End ℝ Z)
    (e : W ≃ₗ[ℝ] Z) (he : ∀ z w,e (σ z w)=τ z (e w)) (z : A) (w : Z) :
    e.symm (τ z w)=σ z (e.symm w) := by
  apply e.injective
  rw [e.apply_symm_apply,he,e.apply_symm_apply]

def algebraIntertwinerTargetEquiv (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (σ : A →ₐ[ℝ] Module.End ℝ W) (τ : A →ₐ[ℝ] Module.End ℝ Z)
    (e : W ≃ₗ[ℝ] Z) (he : ∀ z w,e (σ z w)=τ z (e w)) :
    algebraIntertwinerSpace ρ σ ≃ₗ[ℝ] algebraIntertwinerSpace ρ τ where
  toFun f := ⟨e.toLinearMap.comp f.val,by
    intro z v
    change e (f.val (ρ z v))=τ z (e (f.val v))
    rw [f.property,he]⟩
  invFun g := ⟨e.symm.toLinearMap.comp g.val,by
    intro z v
    change e.symm (g.val (ρ z v))=σ z (e.symm (g.val v))
    rw [g.property,algebraIntertwinerEquiv_inverse σ τ e he]⟩
  left_inv f := by apply Subtype.ext;ext v;exact e.symm_apply_apply (f.val v)
  right_inv g := by apply Subtype.ext;ext v;exact e.apply_symm_apply (g.val v)
  map_add' f g := by apply Subtype.ext;ext v;exact e.map_add _ _
  map_smul' a f := by apply Subtype.ext;ext v;exact e.map_smul a _

end AMSPhysical

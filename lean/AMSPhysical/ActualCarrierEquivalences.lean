import ActualVertexTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

def ActualHighestCarrier.equivTo (hq : q≠0) (C D : ActualHighestCarrier q n lam) : C.space ≃ₗ[ℝ] D.space :=
  LinearEquiv.ofLinear (C.mapTo hq D) (D.mapTo hq C)
    ((D.mapTo_comp hq C D).trans (D.mapTo_self hq))
    ((C.mapTo_comp hq D C).trans (C.mapTo_self hq))

theorem ActualHighestCarrier.equivTo_apply (hq : q≠0) (C D : ActualHighestCarrier q n lam) (v : C.space) :
    C.equivTo hq D v=C.mapTo hq D v := rfl

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem highestSpace_equiv_mem (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (E : V ≃ₗ[ℝ] W)
    (hE : ∀ z v,E (ρ z v)=σ z (E v)) (v : V)
    (hv : v∈typeAHighestSpace q n ρ lam) : E v∈typeAHighestSpace q n σ lam := by
  obtain ⟨hRaise,hCartan⟩:=(mem_typeAHighestSpace q n ρ lam v).mp hv
  apply (mem_typeAHighestSpace q n σ lam _).mpr
  constructor
  · intro i;rw [← hE,hRaise,map_zero]
  · intro i;rw [← hE,hCartan,map_smul]

def highestSpaceEquiv (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (E : V ≃ₗ[ℝ] W)
    (hE : ∀ z v,E (ρ z v)=σ z (E v)) :
    typeAHighestSpace q n ρ lam ≃ₗ[ℝ] typeAHighestSpace q n σ lam where
  toFun v := ⟨E v.val,highestSpace_equiv_mem ρ σ E hE v.val v.property⟩
  invFun w := ⟨E.symm w.val,highestSpace_equiv_mem σ ρ E.symm (by
    intro z v
    apply E.injective
    simp only [LinearEquiv.apply_symm_apply,hE]) w.val w.property⟩
  left_inv v := by apply Subtype.ext;exact E.symm_apply_apply v.val
  right_inv w := by apply Subtype.ext;exact E.apply_symm_apply w.val
  map_add' v w := by apply Subtype.ext;exact E.map_add v.val w.val
  map_smul' a v := by apply Subtype.ext;exact E.map_smul a v.val

theorem actualVertex_highest_finrank (hq : q≠0) {a b : Fin n → ℤ}
    (A : ActualHighestCarrier q n a) (B : ActualHighestCarrier q n b) (mu : Fin n → ℤ) :
    Module.finrank ℝ (typeAHighestSpace q n (actualVertexAction hq A.irrep B.irrep) mu) =
      Module.finrank ℝ (typeAHighestSpace q n
        (typeATensorRepresentation q hq n A.frame.action B.frame.action) mu) := by
  let E:=TensorProduct.congr (A.equivTo hq (fixedActualCarrier A.irrep))
    (B.equivTo hq (fixedActualCarrier B.irrep))
  have hE : ∀ z v,E (typeATensorRepresentation q hq n A.frame.action B.frame.action z v)=
      actualVertexAction hq A.irrep B.irrep z (E v) := by
    intro z v
    exact typeA_intertwiner_tensor q hq n A.frame.action B.frame.action
      (fixedActualCarrier A.irrep).frame.action (fixedActualCarrier B.irrep).frame.action
      (A.mapTo hq _) (B.mapTo hq _) (A.mapTo_intertwines hq _) (B.mapTo_intertwines hq _) z v
  exact (highestSpaceEquiv (lam:=mu) _ _ E hE).finrank_eq.symm

end AMSPhysical
#print axioms AMSPhysical.actualVertex_highest_finrank

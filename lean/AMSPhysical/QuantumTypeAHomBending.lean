import QuantumTypeAUnbending
import AlgebraIntertwinerSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W I : Type*}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [Fintype I] [DecidableEq I]

/-- The actual finite quantum-group Hom spaces are related by the independently
proved invariant cup, invariant evaluation, and literal snake identities. -/
def typeARightBendingEquiv (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ X) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (τ κ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (b : Module.Basis I ℝ V) (c d : I → ℝ) (hcd : ∀ i,c i*d i=1)
    (hc : ∀ z,typeATensorRepresentation q hq n κ τ z (diagonalCoevaluation b c)=
      typeAQuantumCounit q n z • diagonalCoevaluation b c)
    (hd : ∀ z v,diagonalEvaluation b d (typeATensorRepresentation q hq n τ κ z v)=
      typeAQuantumCounit q n z*diagonalEvaluation b d v) :
    algebraIntertwinerSpace (typeATensorRepresentation q hq n ρ κ) σ ≃ₗ[ℝ]
      algebraIntertwinerSpace ρ (typeATensorRepresentation q hq n σ τ) where
  toFun f := ⟨bendRight f.val (diagonalCoevaluation b c),
    typeA_bendRight_intertwines q hq n ρ σ κ τ f.val (diagonalCoevaluation b c) f.property hc⟩
  invFun g := ⟨unbendRight g.val (diagonalEvaluation b d),
    typeA_unbendRight_intertwines q hq n ρ σ τ κ g.val (diagonalEvaluation b d) g.property hd⟩
  left_inv f := Subtype.ext (unbendRight_bendRight_diagonal b c d hcd f.val)
  right_inv g := Subtype.ext (bendRight_unbendRight_diagonal b c d hcd g.val)
  map_add' f g := by
    apply Subtype.ext
    exact (finiteRightBendingEquiv (X:=X) (W:=W) b c d hcd).map_add f.val g.val
  map_smul' a f := by
    apply Subtype.ext
    exact (finiteRightBendingEquiv (X:=X) (W:=W) b c d hcd).map_smul a f.val

end AMSPhysical
#print axioms AMSPhysical.typeARightBendingEquiv

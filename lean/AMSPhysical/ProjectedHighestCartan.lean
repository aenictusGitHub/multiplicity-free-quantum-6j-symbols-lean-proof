import HighestFunctionalCartan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W Z : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

theorem projected_highest_Cartan (q : ℝ) (hq : q≠0) (n : ℕ) (lam mu : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n Z mu)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (F : Z →ₗ[ℝ] V ⊗[ℝ] W)
    (hF : ∀ z v,F (Y.action z v)=typeATensorRepresentation q hq n X.action σ z (F v)) (i : Fin n) :
    σ (typeAAlgebraGenerator q n i 2) (tensorFirstFunctional (X.pairing X.highest) (F Y.highest)) =
      q^(mu i-lam i) • tensorFirstFunctional (X.pairing X.highest) (F Y.highest) := by
  have he:=congrArg (tensorFirstFunctional (X.pairing X.highest))
    (hF (typeAAlgebraGenerator q n i 2) Y.highest)
  rw [Y.highestK,map_smul,map_smul,
    tensorFirstFunctional_K q hq n X.action σ (X.pairing X.highest) i (q^(lam i))
      (X.highest_functional_K i)] at he
  apply smul_right_injective _ (zpow_ne_zero (lam i) hq)
  dsimp only
  rw [← he,smul_smul,← zpow_add₀ hq]
  congr 1
  ring

end AMSPhysical
#print axioms AMSPhysical.projected_highest_Cartan

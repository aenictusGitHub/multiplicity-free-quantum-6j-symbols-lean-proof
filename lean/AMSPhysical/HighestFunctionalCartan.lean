import TensorHighestFunctional
import ActualHighestCarrier

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem CompactHighestRealization.highest_functional_K {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (X : CompactHighestRealization q n V lam) (i : Fin n) (v : V) :
    X.pairing X.highest (X.action (typeAAlgebraGenerator q n i 2) v) =
      q^(lam i)*X.pairing X.highest v := by
  rw [← X.compact.adjK i X.highest v,X.highestK,map_smul,LinearMap.smul_apply,smul_eq_mul]

theorem ActualHighestCarrier.mapTo_highest_functional {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (hq : q≠0) (C D : ActualHighestCarrier q n lam) (v : C.space) :
    D.frame.pairing D.frame.highest (C.mapTo hq D v)=C.frame.pairing C.frame.highest v := by
  have he:=C.mapTo_isometry hq D C.frame.highest v
  rw [C.mapTo_highest] at he
  exact he

theorem tensorFirstFunctional_K (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V →ₗ[ℝ] ℝ) (i : Fin n) (a : ℝ)
    (hK : ∀ x,e (ρ (typeAAlgebraGenerator q n i 2) x)=a*e x) (v : V ⊗[ℝ] W) :
    tensorFirstFunctional e (typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 2) v) =
      a • σ (typeAAlgebraGenerator q n i 2) (tensorFirstFunctional e v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw,smul_add]
  | tmul x y =>
    rw [typeATensorRepresentation_K,tensorFirstFunctional_tmul,tensorFirstFunctional_tmul,
      hK,map_smul,smul_smul]

end AMSPhysical
#print axioms AMSPhysical.ActualHighestCarrier.mapTo_highest_functional

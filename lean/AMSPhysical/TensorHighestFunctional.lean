import QuantumTypeATensorRepresentation
import QuantumTypeALoweringWords
import Mathlib.LinearAlgebra.TensorProduct.Associator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def tensorFirstFunctional (e : V →ₗ[ℝ] ℝ) : V ⊗[ℝ] W →ₗ[ℝ] W :=
  (TensorProduct.lid ℝ W).toLinearMap.comp (TensorProduct.map e LinearMap.id)

def tensorLastFunctional (e : V →ₗ[ℝ] ℝ) : W ⊗[ℝ] V →ₗ[ℝ] W :=
  (TensorProduct.rid ℝ W).toLinearMap.comp (TensorProduct.map LinearMap.id e)

theorem tensorFirstFunctional_tmul (e : V →ₗ[ℝ] ℝ) (x : V) (y : W) :
    tensorFirstFunctional e (x ⊗ₜ[ℝ] y)=e x • y := rfl

theorem tensorLastFunctional_tmul (e : V →ₗ[ℝ] ℝ) (y : W) (x : V) :
    tensorLastFunctional e (y ⊗ₜ[ℝ] x)=e x • y := by
  simp only [tensorLastFunctional,LinearMap.comp_apply,TensorProduct.map_tmul,
    LinearMap.id_apply,LinearEquiv.coe_coe,TensorProduct.rid_tmul]

theorem tensorFirstFunctional_F (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V →ₗ[ℝ] ℝ) (i : Fin n) (a : ℝ)
    (hF : ∀ x,e (ρ (typeAAlgebraGenerator q n i 1) x)=0)
    (hK : ∀ x,e (ρ (typeAAlgebraGenerator q n i 3) x)=a*e x) (v : V ⊗[ℝ] W) :
    tensorFirstFunctional e (typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 1) v) =
      a • σ (typeAAlgebraGenerator q n i 1) (tensorFirstFunctional e v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw,smul_add]
  | tmul x y =>
    rw [typeATensorRepresentation_F,map_add,tensorFirstFunctional_tmul,tensorFirstFunctional_tmul,
      tensorFirstFunctional_tmul,hF,hK,zero_smul,zero_add,map_smul,smul_smul]

theorem tensorLastFunctional_F (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V →ₗ[ℝ] ℝ) (i : Fin n)
    (hF : ∀ x,e (ρ (typeAAlgebraGenerator q n i 1) x)=0) (v : W ⊗[ℝ] V) :
    tensorLastFunctional e (typeATensorRepresentation q hq n σ ρ (typeAAlgebraGenerator q n i 1) v) =
      σ (typeAAlgebraGenerator q n i 1) (tensorLastFunctional e v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul y x =>
    rw [typeATensorRepresentation_F,map_add,tensorLastFunctional_tmul,tensorLastFunctional_tmul,
      tensorLastFunctional_tmul,hF,zero_smul,add_zero,map_smul]

theorem tensorFirstFunctional_lowering (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V →ₗ[ℝ] ℝ) (a : Fin n → ℝ)
    (hF : ∀ i x,e (ρ (typeAAlgebraGenerator q n i 1) x)=0)
    (hK : ∀ i x,e (ρ (typeAAlgebraGenerator q n i 3) x)=a i*e x)
    (x : V) (hx : e x=1) (y : W) (w : List (Fin n)) :
    tensorFirstFunctional e (typeALoweredVector q n (typeATensorRepresentation q hq n ρ σ) (x ⊗ₜ[ℝ] y) w) =
      (w.map a).prod • typeALoweredVector q n σ y w := by
  induction w with
  | nil => simp only [typeALoweredVector_nil,tensorFirstFunctional_tmul,hx,one_smul,List.map_nil,List.prod_nil]
  | cons i w ih =>
    rw [typeALoweredVector_cons,tensorFirstFunctional_F q hq n ρ σ e i (a i) (hF i) (hK i),
      ih,map_smul,smul_smul,List.map_cons,List.prod_cons,typeALoweredVector_cons]

theorem tensorLastFunctional_lowering (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V →ₗ[ℝ] ℝ) (hF : ∀ i x,e (ρ (typeAAlgebraGenerator q n i 1) x)=0)
    (x : V) (hx : e x=1) (y : W) (w : List (Fin n)) :
    tensorLastFunctional e (typeALoweredVector q n (typeATensorRepresentation q hq n σ ρ) (y ⊗ₜ[ℝ] x) w) =
      typeALoweredVector q n σ y w := by
  induction w with
  | nil => simp only [typeALoweredVector_nil,tensorLastFunctional_tmul,hx,one_smul]
  | cons i w ih => rw [typeALoweredVector_cons,tensorLastFunctional_F q hq n ρ σ e i (hF i),ih,typeALoweredVector_cons]

end AMSPhysical
#print axioms AMSPhysical.tensorFirstFunctional_lowering
#print axioms AMSPhysical.tensorLastFunctional_lowering

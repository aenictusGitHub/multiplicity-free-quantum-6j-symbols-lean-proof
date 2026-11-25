import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {V W I J:Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem unitsSMul_operator_coordinate (a:Module.Basis I ℝ V) (b:Module.Basis J ℝ W)
    (u:I → ℝˣ) (v:J → ℝˣ) (T:V →ₗ[ℝ] W) (i:I) (j:J) :
    b.repr (T (a i)) j=(u i:ℝ)⁻¹*(v j:ℝ)*
      (b.unitsSMul v).repr (T ((a.unitsSMul u) i)) j := by
  rw [Module.Basis.unitsSMul_apply,Module.Basis.repr_unitsSMul]
  simp only [Units.smul_def,Units.val_inv_eq_inv_val,map_smul,Finsupp.smul_apply,smul_eq_mul]
  field_simp [(u i).ne_zero,(v j).ne_zero]

end AMSPhysical
#print axioms AMSPhysical.unitsSMul_operator_coordinate

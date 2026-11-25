import BilinearAdjoint
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {I V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Agreement of all spanning-family Gram entries gives agreement on every
finite linear combination, without an independence assumption. -/
theorem linearCombination_pair_congr (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (v : I → V) (w : I → W) (h : ∀ i j,B (v i) (v j)=C (w i) (w j)) (f g : I →₀ ℝ) :
    B (Finsupp.linearCombination ℝ v f) (Finsupp.linearCombination ℝ v g)=
      C (Finsupp.linearCombination ℝ w f) (Finsupp.linearCombination ℝ w g) := by
  classical
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,LinearMap.sum_apply,
    map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j i]

/-- Positivity turns Gram agreement into equality of all linear relations. -/
theorem linearCombination_kernels_eq (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (v : I → V) (w : I → W) (h : ∀ i j,B (v i) (v j)=C (w i) (w j)) :
    LinearMap.ker (Finsupp.linearCombination ℝ v)=LinearMap.ker (Finsupp.linearCombination ℝ w) := by
  ext f
  simp only [LinearMap.mem_ker]
  have he := linearCombination_pair_congr B C v w h f f
  constructor
  · intro hf
    apply hC
    rw [hf,map_zero] at he
    exact he.symm
  · intro hf
    apply hB
    rw [hf,map_zero] at he
    exact he

end AMSPhysical
#print axioms AMSPhysical.linearCombination_kernels_eq

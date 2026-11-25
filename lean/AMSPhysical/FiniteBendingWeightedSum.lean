import FiniteBendingMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W I J K:Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

theorem bendRight_metric_weighted_sum (a:Module.Basis I ℝ X) (b:Module.Basis J ℝ V) (t:Module.Basis K ℝ W)
    (u:I → ℝ) (v c z:J → ℝ) (w:K → ℝ) (e:I → ℝ) (f:J → ℝ) (N:ℝ)
    (hu:∀ i,u i≠0) (_hv:∀ j,v j≠0) (hc:∀ j,c j*c j*z j=f j/v j)
    (T:X ⊗[ℝ] V →ₗ[ℝ] W)
    (hN:∀ i,tensorWeightedBilin t b w z (bendRight T (diagonalCoevaluation b c) (a i))
      (bendRight T (diagonalCoevaluation b c) (a i))=N*u i) :
    N*(∑ i,e i)=∑ p:I×J,e p.1*f p.2/(u p.1*v p.2)*
      finiteWeightedPair w t.equivFun.toLinearMap
        (T (a p.1 ⊗ₜ[ℝ] b p.2)) (T (a p.1 ⊗ₜ[ℝ] b p.2)) := by
  calc
    _=∑ i,e i/u i*(N*u i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hu i]
    _=∑ i,e i/u i*tensorWeightedBilin t b w z (bendRight T (diagonalCoevaluation b c) (a i))
        (bendRight T (diagonalCoevaluation b c) (a i)) := by simp only [hN]
    _=∑ i,∑ j,e i*f j/(u i*v j)*finiteWeightedPair w t.equivFun.toLinearMap
        (T (a i ⊗ₜ[ℝ] b j)) (T (a i ⊗ₜ[ℝ] b j)) := by
      simp only [bendRight_diagonal_metric,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _=e i/u i*(c j*c j*z j)*finiteWeightedPair w t.equivFun.toLinearMap
          (T (a i ⊗ₜ[ℝ] b j)) (T (a i ⊗ₜ[ℝ] b j)) := by ring
        _=e i/u i*(f j/v j)*finiteWeightedPair w t.equivFun.toLinearMap
          (T (a i ⊗ₜ[ℝ] b j)) (T (a i ⊗ₜ[ℝ] b j)) := by rw [hc]
        _=_ := by ring
    _=_ := by rw [Fintype.sum_prod_type]

end AMSPhysical
#print axioms AMSPhysical.bendRight_metric_weighted_sum

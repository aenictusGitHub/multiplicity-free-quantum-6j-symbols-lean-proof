import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem definiteBilinear_injective (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) : Function.Injective B := by
  intro v w he
  have hz : B (v-w)=0 := by rw [map_sub,he,sub_self]
  have hh:=congrArg (fun f : Module.Dual ℝ V =>f (v-w)) hz
  have hd : v-w=0 := hB _ (by simpa using hh)
  exact sub_eq_zero.mp hd

/-- Every actual definite finite-dimensional bilinear form yields a
constructed perfect duality, including on restricted physical irrep carriers. -/
def definiteBilinearDuality [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) : V ≃ₗ[ℝ] Module.Dual ℝ V :=
  LinearEquiv.ofBijective B ⟨definiteBilinear_injective B hB,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K:=ℝ) (V:=V)).symm).mp (definiteBilinear_injective B hB)⟩

end AMSPhysical

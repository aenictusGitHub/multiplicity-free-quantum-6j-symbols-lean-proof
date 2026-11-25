import QuantumMixedRawAdjunction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFiniteRawAnnihilation_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l m : ℕ) (z : UqTypeA q n)
    (u : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    mixedFiniteRawAnnihilation q n l m
        (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) z u)=
      typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
        (mixedFiniteRawAnnihilation q n l m u) := by
  have h:=mixedFiniteContraction_intertwines q hq hq1 n l m z u
  simp only [mixedFiniteContraction_eq_raw q hq hq1,map_smul] at h
  exact smul_right_injective _ (ne_of_gt (mixedAnnihilationScale_pos q hq hq1 n l m)) h

/-- The independently constructed raw radial operator is self-adjoint for
the actual positive compact tensor metric. -/
theorem mixedFiniteRawRadial_selfAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (u v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    mixedTensorBilin q n (l+1) (m+1)
        (mixedFiniteCreation q n l m (mixedFiniteRawAnnihilation q n l m u)) v=
      mixedTensorBilin q n (l+1) (m+1) u
        (mixedFiniteCreation q n l m (mixedFiniteRawAnnihilation q n l m v)) := by
  have h:=mixedFiniteRawAnnihilation_adjoint q hq hq1 n l m
    (mixedFiniteRawAnnihilation q n l m u) v
  have h':=mixedFiniteRawAnnihilation_adjoint q hq hq1 n l m
    (mixedFiniteRawAnnihilation q n l m v) u
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h h'
  rw [mixedTensorBilin_symm q n l m] at h
  exact h.trans (h'.symm.trans (mixedTensorBilin_symm q n (l+1) (m+1) _ _))

end AMSPhysical

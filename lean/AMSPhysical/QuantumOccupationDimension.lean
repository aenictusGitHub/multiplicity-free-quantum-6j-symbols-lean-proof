import QuantumOccupationCharacter
import Mathlib.Data.Nat.Choose.Cast

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteOccupationCartan_one (L : ℕ) (h : ι → ℤ) : finiteOccupationCartan 1 L h=1 := by
  apply (quantumOccupationBasis (K:=ℝ) (ι:=ι) L).ext
  intro x
  rw [finiteOccupationCartan_basis]
  simp only [one_zpow,one_smul,Module.End.one_apply]

theorem qfactorial_at_one (L : ℕ) : qfactorial 1 L=(L.factorial:ℝ) := by
  induction L with
  | zero => simp [qfactorial_zero]
  | succ L ih =>
    rw [qfactorial_succ,ih,qnum_one,Nat.factorial_succ]
    push_cast
    ring

/-- The constructed symmetric module has the expected ordinary Weyl dimension. -/
theorem quantumOccupationSpace_finrank (n L : ℕ) :
    Module.finrank ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L)=(n+L).choose L := by
  have h := inversePivotal_trace_factorial 1 (by norm_num) n L
  rw [finiteOccupationCartan_one,LinearMap.trace_one,qfactorial_at_one,qfactorial_at_one,qfactorial_at_one] at h
  have hc : ((n+L).choose L:ℝ)*(n.factorial:ℝ)*(L.factorial:ℝ)=((n+L).factorial:ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n L
  have hF : (n.factorial:ℝ)*(L.factorial:ℝ)≠0 := by positivity
  have hcast : (Module.finrank ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L):ℝ)=((n+L).choose L:ℝ) := by
    rw [h]
    apply (div_eq_iff hF).mpr
    linear_combination -hc
  exact_mod_cast hcast

end AMSPhysical

#print axioms AMSPhysical.quantumOccupationSpace_finrank

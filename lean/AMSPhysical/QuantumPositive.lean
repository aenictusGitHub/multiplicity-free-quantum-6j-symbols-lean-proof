import QuantumIrreducible
import Normalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

theorem qInteger_denominator_ne_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) : q-q⁻¹≠0 := by
  intro he
  have hh : q=q⁻¹ := sub_eq_zero.mp he
  have hs : q*q=1 := by calc
    q*q=q*q⁻¹ := by rw [← hh]
    _=1 := mul_inv_cancel₀ (ne_of_gt hq)
  have heq : q=1 := (sq_eq_sq₀ hq.le zero_le_one).mp (by nlinarith)
  exact hq1 heq

theorem qInteger_pos_real (q : ℝ) (hq : 0<q) (hq1 : q≠1) (j : ℤ) (hj : 0<j) :
    0<qInteger q j := by
  have hn : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj.le
  have he := qnum_eq_standard q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) j.toNat
  have hp := qnum_pos q hq j.toNat (by omega)
  have heq : qInteger q (j.toNat:ℤ)=qnum q j.toNat := by
    rw [he]
    simp only [qInteger,zpow_natCast]
  rw [hn] at heq
  rw [heq]
  exact hp

/-- Irreducibility for every positive real deformation parameter away from one. -/
theorem quantumEF_irreducible_real (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l : ℕ)
    (S : Submodule ℝ (WeightModule ℝ)) (hS : S≤finiteWeightSpace l)
    (hE : ∀ p∈S,quantumE q p∈S) (hF : ∀ p∈S,quantumF q l p∈S) :
    S=⊥ ∨ S=finiteWeightSpace l :=
  quantumEF_irreducible q l (fun j hj _ => ne_of_gt (qInteger_pos_real q hq hq1 j hj)) S hS hE hF

end AMSPhysical

#print axioms AMSPhysical.quantumEF_irreducible_real

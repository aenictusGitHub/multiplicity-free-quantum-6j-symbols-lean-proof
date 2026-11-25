import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology

/-- Equality up to real signs has one global analytic sign, even across zeros.
The nonzero calibration point fixes that sign. -/
theorem analytic_square_equality_calibrated (U : Set ℝ) (hU : IsOpen U)
    (hconn : IsPreconnected U) (f g : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hsq : ∀ t∈U,(f t)^2=(g t)^2) (t₀ : ℝ) (h₀ : t₀∈U)
    (he : f t₀=g t₀) (hne : f t₀≠0) : EqOn f g U := by
  have hsum : f t₀+g t₀≠0 := by
    rw [← he]
    intro hz
    apply hne
    linarith
  have hnear : ∀ᶠ t in nhds t₀,f t+g t≠0 :=
    ((hf t₀ h₀).continuousAt.add (hg t₀ h₀).continuousAt).eventually_ne hsum
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h₀
  filter_upwards [hnear,hU.mem_nhds h₀] with t ht htu
  have hprod : (f t-g t)*(f t+g t)=0 := by nlinarith [hsq t htu]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right ht)

/-- A constant signed gauge can be calibrated at any nonzero point once actual
real-analytic recoupling entries and equality of their squares are established. -/
theorem analytic_signed_equality_calibrated (U : Set ℝ) (hU : IsOpen U)
    (hconn : IsPreconnected U) (f g : ℝ → ℝ) (s : ℝ) (hs : s^2=1)
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hsq : ∀ t∈U,(f t)^2=(g t)^2) (t₀ : ℝ) (h₀ : t₀∈U)
    (he : f t₀=s*g t₀) (hne : f t₀≠0) : EqOn f (fun t => s*g t) U := by
  apply analytic_square_equality_calibrated U hU hconn f (fun t => s*g t) hf
    (analyticOnNhd_const.mul hg) _ t₀ h₀ he hne
  intro t ht
  rw [mul_pow,hs,one_mul]
  exact hsq t ht

end AMSPhysical

#print axioms AMSPhysical.analytic_signed_equality_calibrated

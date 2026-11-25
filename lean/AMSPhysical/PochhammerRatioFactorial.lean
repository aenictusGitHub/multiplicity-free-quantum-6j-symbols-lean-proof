import PositivePochhammerFactorial
import SearsFactorialTerm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def positivePochPhase (q : ℝ) (a k : ℕ) : ℝ :=
  (-(q-q⁻¹))^k*q^(((a:ℤ)+1)*(k:ℤ)+(k.choose 2:ℤ))

theorem qPochhammer_positive_phase (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a k : ℕ) :
    qPochhammer (q^2) (q^(2*((a:ℤ)+1))) k=
      positivePochPhase q a k*(qfactorial q (a+k)/qfactorial q a) := by
  rw [qPochhammer_positive_factorial q hq hq1]
  unfold positivePochPhase
  ring

/-- A balanced quotient of positive and negative integral parameters has no
remaining power of the deformation parameter. -/
theorem qPochhammer_balanced_factorial_ratio (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b c d u : ℕ) (hub : u≤b) (huc : u≤c) (hbal : a+c=b+d) :
    qPochhammer (q^2) (q^(2*((a:ℤ)+1))) u*qPochhammer (q^2) (q^(-2*(b:ℤ))) u/
      (qPochhammer (q^2) (q^(-2*(c:ℤ))) u*qPochhammer (q^2) (q^(2*((d:ℤ)+1))) u)=
    qfactorial q (a+u)*qfactorial q b*qfactorial q (c-u)*qfactorial q d/
      (qfactorial q a*qfactorial q (b-u)*qfactorial q c*qfactorial q (d+u)) := by
  have hq0 := ne_of_gt hq
  have hD := qInteger_denominator_ne_zero q hq hq1
  have hp : positivePochPhase q a u*negativePochPhase q b u=
      negativePochPhase q c u*positivePochPhase q d u := by
    have hphase : q^(((a:ℤ)+1)*(u:ℤ)+(u.choose 2:ℤ))*q^(-(b:ℤ)*(u:ℤ)+(u.choose 2:ℤ))=
        q^(-(c:ℤ)*(u:ℤ)+(u.choose 2:ℤ))*q^(((d:ℤ)+1)*(u:ℤ)+(u.choose 2:ℤ)) := by
      rw [← zpow_add₀ hq0,← zpow_add₀ hq0]
      congr 1
      have hb : (a:ℤ)+(c:ℤ)=(b:ℤ)+(d:ℤ) := by exact_mod_cast hbal
      linear_combination (u:ℤ)*hb
    unfold positivePochPhase negativePochPhase
    linear_combination (-(q-q⁻¹))^u*(q-q⁻¹)^u*hphase
  have hne : negativePochPhase q c u*positivePochPhase q d u≠0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD) (zpow_ne_zero _ hq0))
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hD)) (zpow_ne_zero _ hq0))
  rw [qPochhammer_positive_phase q hq hq1 a u,
    qPochhammer_negative_phase_factorial q hq hq1 b u hub,
    qPochhammer_negative_phase_factorial q hq hq1 c u huc,
    qPochhammer_positive_phase q hq hq1 d u]
  calc
    _ = (positivePochPhase q a u*negativePochPhase q b u/
      (negativePochPhase q c u*positivePochPhase q d u))*
      (qfactorial q (a+u)*qfactorial q b*qfactorial q (c-u)*qfactorial q d/
        (qfactorial q a*qfactorial q (b-u)*qfactorial q c*qfactorial q (d+u))) := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    _ = _ := by rw [hp,div_self hne,one_mul]

end AMSPhysical

#print axioms AMSPhysical.qPochhammer_balanced_factorial_ratio

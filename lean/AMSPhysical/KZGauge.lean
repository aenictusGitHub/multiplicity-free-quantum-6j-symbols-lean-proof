import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
namespace AMSPhysical

/-- Scalar gauge for adding scalar residues at 0 and 1. -/
def scalarGauge (α β z : ℂ) : ℂ :=
  Complex.exp (α*Complex.log z+β*Complex.log (1-z))

theorem scalarGauge_ne_zero (α β z : ℂ) : scalarGauge α β z≠0 :=
  Complex.exp_ne_zero _

theorem scalarGauge_hasDerivAt (α β z : ℂ)
    (hz : z∈Complex.slitPlane) (h₁z : 1-z∈Complex.slitPlane) :
    HasDerivAt (scalarGauge α β)
      ((α/z+β/(z-1))*scalarGauge α β z) z := by
  have h0 := (Complex.hasDerivAt_log hz).const_mul α
  have h1 := (((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).clog h₁z).const_mul β
  have hh : (0-1:ℂ)/(1-z) = (z-1)⁻¹ := by
    simp only [zero_sub,neg_div,one_div]
    rw [← inv_neg,neg_sub]
  convert (h0.add h1).cexp using 1
  dsimp [scalarGauge]
  rw [hh]
  simp only [div_eq_mul_inv]
  ring

theorem scalarGauge_left_cancel (α β z : ℂ) :
    Complex.exp (-α*Complex.log z)*scalarGauge α β z =
      Complex.exp (β*Complex.log (1-z)) := by
  unfold scalarGauge
  rw [← Complex.exp_add]
  congr 1
  ring

theorem scalarGauge_right_cancel (α β z : ℂ) :
    Complex.exp (-β*Complex.log (1-z))*scalarGauge α β z =
      Complex.exp (α*Complex.log z) := by
  unfold scalarGauge
  rw [← Complex.exp_add]
  congr 1
  ring

open Filter in
theorem scalarGauge_left_limit (α β : ℂ) :
    Tendsto (fun z => Complex.exp (-α*Complex.log z)*scalarGauge α β z)
      (nhds 0) (nhds 1) := by
  simp_rw [scalarGauge_left_cancel]
  have hl : ContinuousAt (fun z : ℂ => Complex.log (1-z)) 0 :=
    (Complex.hasDerivAt_log (by simp)).continuousAt.comp (continuousAt_const.sub continuousAt_id)
  have hc : ContinuousAt (fun z : ℂ => Complex.exp (β*Complex.log (1-z))) 0 :=
    (continuousAt_const.mul hl).cexp
  simpa using hc.tendsto

open Filter in
theorem scalarGauge_right_limit (α β : ℂ) :
    Tendsto (fun z => Complex.exp (-β*Complex.log (1-z))*scalarGauge α β z)
      (nhds 1) (nhds 1) := by
  simp_rw [scalarGauge_right_cancel]
  have hl : ContinuousAt Complex.log (1:ℂ) := (Complex.hasDerivAt_log (by simp)).continuousAt
  have hc : ContinuousAt (fun z : ℂ => Complex.exp (α*Complex.log z)) 1 :=
    (continuousAt_const.mul hl).cexp
  simpa using hc.tendsto

section ODE
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def kzCoefficient (a b : A) (z : ℂ) : A := z⁻¹ • a+(z-1)⁻¹ • b

/-- A constant simultaneous intertwiner transports actual KZ solutions. -/
theorem intertwiner_kz_solution (a b a' b' S : A) (z : ℂ) (G : ℂ → A)
    (ha : a'*S=S*a) (hb : b'*S=S*b)
    (hG : HasDerivAt G (kzCoefficient a b z*G z) z) :
    HasDerivAt (fun x => S*G x) (kzCoefficient a' b' z*(S*G z)) z := by
  have hc : kzCoefficient a' b' z*S=S*kzCoefficient a b z := by
    simp only [kzCoefficient,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,ha,hb]
  convert hG.const_mul S using 1
  rw [← mul_assoc, hc, mul_assoc]

/-- The shifted KZ equation is obtained by an actual analytic scalar gauge,
not by assuming a naturality property of an unnamed associator. -/
theorem scalarGauge_kz_solution (a b : A) (α β z : ℂ) (G : ℂ → A)
    (hz : z∈Complex.slitPlane) (h₁z : 1-z∈Complex.slitPlane)
    (hG : HasDerivAt G (kzCoefficient a b z*G z) z) :
    HasDerivAt (fun x => scalarGauge α β x • G x)
      (kzCoefficient (a+α • 1) (b+β • 1) z * (scalarGauge α β z • G z)) z := by
  convert (scalarGauge_hasDerivAt α β z hz h₁z).fun_smul hG using 1
  simp only [kzCoefficient,smul_add,add_mul,mul_add,smul_mul_assoc,
    mul_smul_comm,smul_smul,one_mul,div_eq_mul_inv]
  module

end ODE

/-- Common left gauge factors cancel in the connection matrix, even noncommutatively. -/
theorem common_gauge_connection {G : Type*} [Group G] (s g₀ g₁ : G) :
    (s*g₁)⁻¹*(s*g₀)=g₁⁻¹*g₀ := by simp [mul_assoc]

theorem conjugate_connection {G : Type*} [Group G] (s g₀ g₁ : G) :
    (s*g₁*s⁻¹)⁻¹*(s*g₀*s⁻¹)=s*(g₁⁻¹*g₀)*s⁻¹ := by simp [mul_assoc]

end AMSPhysical

#print axioms AMSPhysical.scalarGauge_hasDerivAt
#print axioms AMSPhysical.scalarGauge_kz_solution
#print axioms AMSPhysical.scalarGauge_left_limit
#print axioms AMSPhysical.scalarGauge_right_limit
#print axioms AMSPhysical.common_gauge_connection

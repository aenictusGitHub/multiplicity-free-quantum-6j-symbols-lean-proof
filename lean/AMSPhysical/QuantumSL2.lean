import QuantumNumbers
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

abbrev WeightModule (K : Type*) [Field K] := ℤ →₀ K

/-- A weighted shift on the independent integer-weight basis. -/
def weightShift (s : ℤ) (w : ℤ → K) : Module.End K (WeightModule K) :=
  Finsupp.lsum K (fun k => LinearMap.toSpanSingleton K _ (Finsupp.single (k+s) (w k)))

@[simp] theorem weightShift_single (s : ℤ) (w : ℤ → K) (k : ℤ) (a : K) :
    weightShift s w (Finsupp.single k a)=Finsupp.single (k+s) (a*w k) := by
  unfold weightShift
  rw [Finsupp.lsum_single]
  simp only [LinearMap.toSpanSingleton_apply,Finsupp.smul_single,smul_eq_mul]

def quantumE (q : K) : Module.End K (WeightModule K) := weightShift (-1) (qInteger q)
def quantumF (q : K) (l : ℤ) : Module.End K (WeightModule K) :=
  weightShift 1 (fun k => qInteger q (l-k))
def quantumK (q : K) (l : ℤ) : Module.End K (WeightModule K) :=
  weightShift 0 (fun k => q^(l-2*k))
def quantumKinv (q : K) (l : ℤ) : Module.End K (WeightModule K) :=
  weightShift 0 (fun k => q^(-(l-2*k)))

theorem quantumK_inverse (q : K) (hq : q≠0) (l : ℤ) :
    quantumK q l*quantumKinv q l=1 := by
  apply Finsupp.lhom_ext
  intro k a
  simp only [Module.End.mul_apply,quantumK,quantumKinv,weightShift_single,add_zero,
    zpow_neg,mul_assoc,inv_mul_cancel₀ (zpow_ne_zero _ hq),mul_one,Module.End.one_apply]

theorem quantumKinv_inverse (q : K) (hq : q≠0) (l : ℤ) :
    quantumKinv q l*quantumK q l=1 := by
  apply Finsupp.lhom_ext
  intro k a
  simp only [Module.End.mul_apply,quantumK,quantumKinv,weightShift_single,add_zero,
    zpow_neg,mul_assoc,mul_inv_cancel₀ (zpow_ne_zero _ hq),mul_one,Module.End.one_apply]

theorem quantumK_E (q : K) (hq : q≠0) (l : ℤ) :
    quantumK q l*quantumE q=q^2 • (quantumE q*quantumK q l) := by
  apply Finsupp.lhom_ext
  intro k a
  simp only [Module.End.mul_apply,quantumK,quantumE,weightShift_single,add_zero,
    LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul]
  have he : l-2*(k+-1)=(l-2*k)+2 := by omega
  rw [he,zpow_add₀ hq]
  simp only [zpow_ofNat]
  apply congrArg (Finsupp.single (k+-1))
  ring

theorem quantumK_F (q : K) (hq : q≠0) (l : ℤ) :
    quantumK q l*quantumF q l=q^(-2:ℤ) • (quantumF q l*quantumK q l) := by
  apply Finsupp.lhom_ext
  intro k a
  simp only [Module.End.mul_apply,quantumK,quantumF,weightShift_single,add_zero,
    LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul]
  have he : l-2*(k+1)=(l-2*k)+(-2) := by omega
  rw [he,zpow_add₀ hq]
  apply congrArg (Finsupp.single (k+1))
  ring

/-- Independently checked U_q(sl_2) defining commutator, on an explicit module. -/
theorem quantum_commutator (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℤ) :
    quantumE q*quantumF q l-quantumF q l*quantumE q=
      (q-q⁻¹)⁻¹ • (quantumK q l-quantumKinv q l) := by
  apply Finsupp.lhom_ext
  intro k a
  simp only [LinearMap.sub_apply,Module.End.mul_apply,quantumE,quantumF,quantumK,quantumKinv,
    weightShift_single,LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul]
  have h₁ : k+1+(-1)=k := by omega
  have h₂ : k+(-1)+1=k := by omega
  rw [h₁,h₂]
  simp only [add_zero,← Finsupp.single_sub]
  have he := qInteger_cross q hq hden k (l-k)
  have hi : l-(k+-1)=(l-k)+1 := by omega
  rw [hi]
  have hj : (l-k)-k=l-2*k := by omega
  rw [hj] at he
  simp only [Finsupp.smul_single,smul_eq_mul]
  apply congrArg (Finsupp.single k)
  calc
    (a*qInteger q (l-k))*qInteger q (k+1)-(a*qInteger q k)*qInteger q (l-k+1) =
        a*(qInteger q (k+1)*qInteger q (l-k)-qInteger q k*qInteger q (l-k+1)) := by ring
    _=a*qInteger q (l-2*k) := by rw [he]
    _=_ := by unfold qInteger; ring

end AMSPhysical

#print axioms AMSPhysical.quantum_commutator

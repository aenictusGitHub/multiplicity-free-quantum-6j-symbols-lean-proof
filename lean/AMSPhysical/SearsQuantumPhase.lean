import PochhammerQuantumFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def negativePochPhase (q : ℝ) (a k : ℕ) : ℝ :=
  (q-q⁻¹)^k*q^(-(a:ℤ)*(k:ℤ)+(k.choose 2:ℤ))
def basePochPhase (q : ℝ) (k : ℕ) : ℝ :=
  (-(q-q⁻¹))^k*q^((k:ℤ)+(k.choose 2:ℤ))

theorem twice_choose_two (k : ℕ) : 2*(k.choose 2:ℤ)=(k:ℤ)*((k:ℤ)-1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one]
    change 2*((k:ℤ)+(k.choose 2:ℤ))=((k:ℤ)+1)*(((k:ℤ)+1)-1)
    nlinarith

theorem sears_scalar_power_phase (D : ℝ) (hD : D≠0) (u k : ℕ) (hk : k≤u) :
    (D^k)^4/((-D)^k*D^k)*(D^(u-k))^2=(-1:ℝ)^k*D^(2*u) := by
  have ht : D^u=D^k*D^(u-k) := by rw [← pow_add];congr 1;omega
  have hu : D^(2*u)=(D^u)^2 := by rw [mul_comm 2 u,pow_mul]
  have hs : ((-1:ℝ)^k)^2=1 := by rw [← pow_mul,mul_comm k 2,pow_mul];norm_num
  rw [hu,ht,neg_pow]
  field_simp [pow_ne_zero k hD,pow_ne_zero k (by norm_num : (-1:ℝ)≠0)]
  linear_combination -hs

theorem qpower_eleven_factors (q : ℝ) (hq : q≠0) (a b c d e f g h i j k : ℤ) :
    (q^a*q^b*q^c*q^d)/(q^e*q^f)*q^g*q^h*q^i*q^j*q^k=
      q^(a+b+c+d-e-f+g+h+i+j+k) := by
  simp only [zpow_add₀ hq,zpow_sub₀ hq,div_eq_mul_inv,mul_inv_rev]
  ring

theorem sears_integer_phase (u r A B M S T k : ℕ) (hk : k≤u)
    (hrel : r+A+B+M+S+1=u+T) :
    (-(u:ℤ)*(k:ℤ)+(k.choose 2:ℤ))+(-(r:ℤ)*(k:ℤ)+(k.choose 2:ℤ))+
      (-(A:ℤ)*(k:ℤ)+(k.choose 2:ℤ))+(-(B:ℤ)*(k:ℤ)+(k.choose 2:ℤ))-
      ((k:ℤ)+(k.choose 2:ℤ))-(-(T:ℤ)*(k:ℤ)+(k.choose 2:ℤ))+
      2*(-(r:ℤ))*((u-k:ℕ):ℤ)+2*((u:ℤ)-(r:ℤ)-(M:ℤ)-(S:ℤ)-1)*(k:ℤ)+
      2*(k:ℤ)*((u-k+1:ℕ):ℤ)+(-(M:ℤ)*((u-k:ℕ):ℤ)+((u-k).choose 2:ℤ))+
      (-(S:ℤ)*((u-k:ℕ):ℤ)+((u-k).choose 2:ℤ))=
      -((M:ℤ)+2*(r:ℤ)+(S:ℤ))*(u:ℤ)+2*(u.choose 2:ℤ) := by
  have h₁ := twice_choose_two k
  have h₂ := twice_choose_two (u-k)
  have h₃ := twice_choose_two u
  have hcast : ((u-k:ℕ):ℤ)=(u:ℤ)-(k:ℤ) := by omega
  have hcast' : ((u-k+1:ℕ):ℤ)=(u:ℤ)-(k:ℤ)+1 := by omega
  have hr : (r:ℤ)+(A:ℤ)+(B:ℤ)+(M:ℤ)+(S:ℤ)+1=(u:ℤ)+(T:ℤ) := by exact_mod_cast hrel
  have hrk := congrArg (fun z : ℤ => z*(k:ℤ)) hr
  rw [hcast] at h₂
  rw [hcast,hcast']
  nlinarith

/-- Complete cancellation of q-powers and deformation denominators in the
physical terminating Sears summand. -/
theorem sears_quantum_phase (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (u r A B M S T k : ℕ) (hk : k≤u) (hrel : r+A+B+M+S+1=u+T) :
    (negativePochPhase q u k*negativePochPhase q r k*negativePochPhase q A k*negativePochPhase q B k)/
      (basePochPhase q k*negativePochPhase q T k)*
      q^(2*(-(r:ℤ))*((u-k:ℕ):ℤ))*q^(2*((u:ℤ)-(r:ℤ)-(M:ℤ)-(S:ℤ)-1)*(k:ℤ))*
      q^(2*(k:ℤ)*((u-k+1:ℕ):ℤ))*negativePochPhase q M (u-k)*negativePochPhase q S (u-k)=
      (-1:ℝ)^k*(q-q⁻¹)^(2*u)*q^(-((M:ℤ)+2*(r:ℤ)+(S:ℤ))*(u:ℤ)+2*(u.choose 2:ℤ)) := by
  have hq0 := ne_of_gt hq
  have hD := qInteger_denominator_ne_zero q hq hq1
  calc
    _ = ((q-q⁻¹)^k)^4/((-(q-q⁻¹))^k*(q-q⁻¹)^k)*((q-q⁻¹)^(u-k))^2*
      ((q^(-(u:ℤ)*(k:ℤ)+(k.choose 2:ℤ))*q^(-(r:ℤ)*(k:ℤ)+(k.choose 2:ℤ))*
        q^(-(A:ℤ)*(k:ℤ)+(k.choose 2:ℤ))*q^(-(B:ℤ)*(k:ℤ)+(k.choose 2:ℤ)))/
        (q^((k:ℤ)+(k.choose 2:ℤ))*q^(-(T:ℤ)*(k:ℤ)+(k.choose 2:ℤ)))*
        q^(2*(-(r:ℤ))*((u-k:ℕ):ℤ))*q^(2*((u:ℤ)-(r:ℤ)-(M:ℤ)-(S:ℤ)-1)*(k:ℤ))*
        q^(2*(k:ℤ)*((u-k+1:ℕ):ℤ))*q^(-(M:ℤ)*((u-k:ℕ):ℤ)+((u-k).choose 2:ℤ))*
        q^(-(S:ℤ)*((u-k:ℕ):ℤ)+((u-k).choose 2:ℤ))) := by
      unfold negativePochPhase basePochPhase
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by
      rw [sears_scalar_power_phase _ hD u k hk,qpower_eleven_factors q hq0,
        sears_integer_phase u r A B M S T k hk hrel]

end AMSPhysical

#print axioms AMSPhysical.sears_quantum_phase

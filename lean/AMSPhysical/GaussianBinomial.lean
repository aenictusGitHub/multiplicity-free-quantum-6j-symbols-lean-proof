import GaussianFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

def gaussianBinomial (Q : ℝ) : ℕ → ℕ → ℝ
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 1
  | n+1,k+1 => gaussianBinomial Q n (k+1)+Q^(n-k)*gaussianBinomial Q n k

theorem gaussianBinomial_zero_right (Q : ℝ) (n : ℕ) : gaussianBinomial Q n 0=1 := by
  cases n <;> rfl

theorem gaussianBinomial_above (Q : ℝ) (n k : ℕ) (hk : n<k) : gaussianBinomial Q n k=0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [gaussianBinomial,ih (k+1) (by omega),ih k (by omega),mul_zero,add_zero]

theorem gaussianBinomial_self (Q : ℝ) (n : ℕ) : gaussianBinomial Q n n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gaussianBinomial,gaussianBinomial_above Q n (n+1) (by omega),ih,Nat.sub_self,pow_zero,one_mul,zero_add]

theorem gaussianBinomial_coefficient (Q : ℝ) (n k : ℕ) (hk : k≤n) :
    gaussianBinomial Q n k=gaussianCoefficient Q (n-k) k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    rw [gaussianBinomial_zero_right,gaussianCoefficient_zero_left]
  | succ n ih =>
    cases k with
    | zero => rw [gaussianBinomial_zero_right,gaussianCoefficient_zero_right]
    | succ k =>
      by_cases hkn : k=n
      · subst k
        rw [gaussianBinomial_self,Nat.sub_self,gaussianCoefficient_zero_left]
      · have hlt : k<n := by omega
        have hs : n+1-(k+1)=(n-k-1)+1 := by omega
        have hs' : n-k=(n-k-1)+1 := by omega
        rw [gaussianBinomial,ih (k+1) (by omega),ih k (by omega),hs,gaussianCoefficient_step]
        have ha : n-(k+1)=n-k-1 := by omega
        rw [ha,hs']
        simp only [Nat.add_sub_cancel]

theorem gaussianBinomial_factorial (q : ℝ) (hq : 0<q) (n k : ℕ) (hk : k≤n) :
    gaussianBinomial (q^2) n k=q^((k*(n-k):ℕ):ℤ)*qfactorial q n/
      (qfactorial q k*qfactorial q (n-k)) := by
  rw [gaussianBinomial_coefficient (q^2) n k hk,gaussianCoefficient_factorial q hq]
  unfold gaussianFactorial
  have hs : n-k+k=n := Nat.sub_add_cancel hk
  rw [hs,Nat.mul_comm (n-k) k,mul_comm (qfactorial q (n-k))]

end AMSPhysical

#print axioms AMSPhysical.gaussianBinomial_factorial

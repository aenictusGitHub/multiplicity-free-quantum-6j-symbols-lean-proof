import GaussianBinomial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem gaussianBinomial_sum_step (Q : ℝ) (n : ℕ) (f : ℕ → V) :
    (∑ k∈Finset.range (n+2),gaussianBinomial Q (n+1) k • f k)=
      (∑ k∈Finset.range (n+1),gaussianBinomial Q n k • f k)+
      ∑ k∈Finset.range (n+1),(Q^(n-k)*gaussianBinomial Q n k) • f (k+1) := by
  rw [Finset.sum_range_succ' (fun k => gaussianBinomial Q (n+1) k • f k) (n+1)]
  simp only [gaussianBinomial,add_smul,Finset.sum_add_distrib,one_smul]
  rw [Finset.sum_range_succ (fun k => gaussianBinomial Q n (k+1) • f (k+1)) n,
    gaussianBinomial_above Q n (n+1) (by omega),zero_smul,add_zero]
  rw [Finset.sum_range_succ' (fun k => gaussianBinomial Q n k • f k) n]
  rw [gaussianBinomial_zero_right,one_smul]
  abel

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem qcommute_pow (Q : ℝ) (X Y : A) (h : Y*X=Q • (X*Y)) (n : ℕ) :
    Y*X^n=Q^n • (X^n*Y) := by
  induction n with
  | zero => simp only [pow_zero,mul_one,one_mul,one_smul]
  | succ n ih =>
    rw [pow_succ,mul_assoc,← mul_assoc Y,ih,smul_mul_assoc,mul_assoc (X^n),h,
      mul_smul_comm,smul_smul,← mul_assoc,pow_succ]

/-- The quantum binomial theorem for genuine noncommuting operators. -/
theorem qcommute_add_pow (Q : ℝ) (X Y : A) (h : Y*X=Q • (X*Y)) (n : ℕ) :
    (X+Y)^n=∑ k∈Finset.range (n+1),gaussianBinomial Q n k • (X^(n-k)*Y^k) := by
  induction n with
  | zero => simp only [Nat.zero_add,Finset.sum_range_one,gaussianBinomial,Nat.sub_self,pow_zero,one_mul,one_smul]
  | succ n ih =>
    rw [pow_succ',ih,Finset.mul_sum]
    let f (k : ℕ) : A := X^(n+1-k)*Y^k
    calc
      _=(∑ k∈Finset.range (n+1),gaussianBinomial Q n k • f k)+
          ∑ k∈Finset.range (n+1),(Q^(n-k)*gaussianBinomial Q n k) • f (k+1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k≤n := by have hh := Finset.mem_range.mp hk;omega
        have hs : n+1-k=(n-k)+1 := by omega
        have hs' : n+1-(k+1)=n-k := by omega
        dsimp only [f]
        rw [hs,hs',mul_smul_comm,add_mul,smul_add]
        congr 1
        · rw [pow_succ',mul_assoc]
        · rw [← mul_assoc,qcommute_pow Q X Y h (n-k),smul_mul_assoc,
            mul_assoc,← pow_succ',smul_smul,mul_comm (gaussianBinomial Q n k)]
      _=∑ k∈Finset.range (n+2),gaussianBinomial Q (n+1) k • f k :=
        (gaussianBinomial_sum_step Q n f).symm

end AMSPhysical

#print axioms AMSPhysical.qcommute_add_pow

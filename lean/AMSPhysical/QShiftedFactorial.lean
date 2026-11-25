import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

def qPochhammer (Q a : ℝ) (n : ℕ) : ℝ := ∏ k∈Finset.range n,(1-a*Q^k)

theorem qPochhammer_zero (Q a : ℝ) : qPochhammer Q a 0=1 := by simp [qPochhammer]

theorem qPochhammer_succ (Q a : ℝ) (n : ℕ) :
    qPochhammer Q a (n+1)=qPochhammer Q a n*(1-a*Q^n) :=
  Finset.prod_range_succ (fun k => 1-a*Q^k) n

theorem qPochhammer_shift (Q a : ℝ) (n : ℕ) :
    (1-a)*qPochhammer Q (a*Q) n=qPochhammer Q a n*(1-a*Q^n) := by
  induction n with
  | zero => simp only [qPochhammer_zero,pow_zero,mul_one,one_mul]
  | succ n ih =>
    calc
      _=((1-a)*qPochhammer Q (a*Q) n)*(1-a*Q^(n+1)) := by
        rw [qPochhammer_succ,pow_succ]
        ring
      _=_ := by rw [ih,qPochhammer_succ]

theorem qPochhammer_ne_zero (Q a : ℝ) (n : ℕ) (h : ∀ k,k<n → 1-a*Q^k≠0) :
    qPochhammer Q a n≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact h k (Finset.mem_range.mp hk)

theorem qPochhammer_terminates (Q : ℝ) (hQ : Q≠0) (n k : ℕ) (hk : n<k) :
    qPochhammer Q (Q^(-(n:ℤ))) k=0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
  have hp : Q^(-(n:ℤ))*Q^n=1 := by
    rw [← zpow_natCast Q n,← zpow_add₀ hQ,neg_add_cancel,zpow_zero]
  rw [hp,sub_self]

theorem qPochhammer_continuous (Q : ℝ) (n : ℕ) : Continuous (fun a : ℝ => qPochhammer Q a n) := by
  unfold qPochhammer
  exact continuous_finset_prod _ (fun k _ => continuous_const.sub (continuous_id.mul continuous_const))

end AMSPhysical

#print axioms AMSPhysical.qPochhammer_shift

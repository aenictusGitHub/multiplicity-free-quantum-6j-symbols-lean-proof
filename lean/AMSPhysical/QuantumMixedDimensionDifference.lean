import QuantumMixedIrrepDimension
import MinimumDiagonalSumInversion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical

theorem symmetricQuantumDimension_zero (q : ℝ) (hq : 0<q) (n : ℕ) : symmetricQuantumDimension q n 0=1 := by
  simp only [symmetricQuantumDimension,Nat.add_zero,qfactorial_zero,mul_one,
    div_self (qfactorial_ne_zero q hq n)]

/-- Closed physical mixed quantum dimension, derived from the actual fusion
trace rather than assumed from a Weyl-character formula. -/
theorem mixedIrrepQuantumDimension_succ (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) :
    mixedIrrepQuantumDimension q hq hq1 n hn (a+1) (b+1)=
      symmetricQuantumDimension q n (a+1)*symmetricQuantumDimension q n (b+1)-
        symmetricQuantumDimension q n a*symmetricQuantumDimension q n b :=
  minimumDiagonalSum_invert_succ (symmetricQuantumDimension q n) (mixedIrrepQuantumDimension q hq hq1 n hn)
    (symmetricQuantumDimension_product_fusion q hq hq1 n hn) a b

theorem mixedIrrepQuantumDimension_left_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (b : ℕ) :
    mixedIrrepQuantumDimension q hq hq1 n hn 0 b=symmetricQuantumDimension q n b := by
  rw [minimumDiagonalSum_left_zero (symmetricQuantumDimension q n) (mixedIrrepQuantumDimension q hq hq1 n hn)
    (symmetricQuantumDimension_product_fusion q hq hq1 n hn) b,symmetricQuantumDimension_zero q hq,one_mul]

theorem mixedIrrepQuantumDimension_right_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a : ℕ) :
    mixedIrrepQuantumDimension q hq hq1 n hn a 0=symmetricQuantumDimension q n a := by
  rw [minimumDiagonalSum_right_zero (symmetricQuantumDimension q n) (mixedIrrepQuantumDimension q hq hq1 n hn)
    (symmetricQuantumDimension_product_fusion q hq hq1 n hn) a,symmetricQuantumDimension_zero q hq,mul_one]

end AMSPhysical
#print axioms AMSPhysical.mixedIrrepQuantumDimension_succ

import QuantumTwoRowIrrepDimension
import TwoRowFusionSumInversion
import QuantumMixedDimensionDifference

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem twoRowIrrepQuantumDimension_succ (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) :
    twoRowIrrepQuantumDimension q hq hq1 n hn a (b+1)=
      symmetricQuantumDimension q n (a+b+1)*symmetricQuantumDimension q n (b+1)-
        symmetricQuantumDimension q n (a+b+2)*symmetricQuantumDimension q n b :=
  twoRowFusionSum_invert_succ (symmetricQuantumDimension q n) (twoRowIrrepQuantumDimension q hq hq1 n hn)
    (symmetricQuantumDimension_product_twoRow_fusion q hq hq1 n hn) a b

theorem twoRowIrrepQuantumDimension_right_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a : ℕ) :
    twoRowIrrepQuantumDimension q hq hq1 n hn a 0=symmetricQuantumDimension q n a := by
  rw [twoRowFusionSum_right_zero (symmetricQuantumDimension q n) (twoRowIrrepQuantumDimension q hq hq1 n hn)
    (symmetricQuantumDimension_product_twoRow_fusion q hq hq1 n hn) a,symmetricQuantumDimension_zero q hq,mul_one]

end AMSPhysical
#print axioms AMSPhysical.twoRowIrrepQuantumDimension_succ

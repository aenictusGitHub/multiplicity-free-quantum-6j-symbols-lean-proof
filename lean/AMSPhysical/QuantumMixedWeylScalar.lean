import QuantumMixedDimensionDifference
import QuantumDimensionProductIdentity

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def mixedWeylDimension (q : ℝ) (n a b : ℕ) : ℝ :=
  qnum q (a+b+n)*qfactorial q (a+n-1)*qfactorial q (b+n-1)/
    (qfactorial q a*qfactorial q b*qfactorial q n*qfactorial q (n-1))

theorem mixedWeylDimension_swap (q : ℝ) (n a b : ℕ) :
    mixedWeylDimension q n a b=mixedWeylDimension q n b a := by
  unfold mixedWeylDimension
  rw [Nat.add_comm a b]
  ring

theorem mixedWeylDimension_left_zero (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (b : ℕ) :
    mixedWeylDimension q n 0 b=symmetricQuantumDimension q n b := by
  have hF : qfactorial q (n+b)=qfactorial q (b+n-1)*qnum q (b+n) := by
    have h:=qfactorial_succ q (b+n-1)
    rw [show b+n-1+1=b+n from by omega] at h
    rw [Nat.add_comm n b]
    exact h
  unfold mixedWeylDimension symmetricQuantumDimension
  simp only [zero_add,qfactorial_zero,one_mul]
  rw [hF]
  field_simp [qfactorial_ne_zero q hq n,qfactorial_ne_zero q hq b,qfactorial_ne_zero q hq (n-1)]

theorem qnum_factorial_ratio (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) :
    qnum q n/(qfactorial q n*qfactorial q n)=1/(qfactorial q n*qfactorial q (n-1)) := by
  have hf : qfactorial q n=qfactorial q (n-1)*qnum q n := by
    have h:=qfactorial_succ q (n-1)
    simpa only [show n-1+1=n from by omega] using h
  field_simp [qfactorial_ne_zero q hq n,qfactorial_ne_zero q hq (n-1)]
  linear_combination -hf

theorem symmetricQuantumDimension_product_difference_factor (q : ℝ) (hq : 0<q)
    (n a b : ℕ) :
    symmetricQuantumDimension q n (a+1)*symmetricQuantumDimension q n (b+1)-
      symmetricQuantumDimension q n a*symmetricQuantumDimension q n b=
      (qfactorial q (n+a)*qfactorial q (n+b)/
        (qfactorial q n*qfactorial q n*qfactorial q (a+1)*qfactorial q (b+1)))*
      (qnum q (n+a+1)*qnum q (n+b+1)-qnum q (a+1)*qnum q (b+1)) := by
  unfold symmetricQuantumDimension
  have ha : n+(a+1)=n+a+1 := by omega
  have hb : n+(b+1)=n+b+1 := by omega
  rw [ha,hb,qfactorial_succ q (n+a),qfactorial_succ q (n+b)]
  rw [qfactorial_succ q a,qfactorial_succ q b]
  field_simp [qfactorial_ne_zero q hq n,qfactorial_ne_zero q hq a,qfactorial_ne_zero q hq b,
    ne_of_gt (qnum_pos q hq (a+1) (by omega)),ne_of_gt (qnum_pos q hq (b+1) (by omega))]

theorem mixedWeylDimension_succ_difference (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) :
    symmetricQuantumDimension q n (a+1)*symmetricQuantumDimension q n (b+1)-
      symmetricQuantumDimension q n a*symmetricQuantumDimension q n b=mixedWeylDimension q n (a+1) (b+1) := by
  rw [symmetricQuantumDimension_product_difference_factor q hq]
  have he:=qnum_shift_product q hq hq1 (a+1) (b+1) n
  have ha : a+1+n=n+a+1 := by omega
  have hb : b+1+n=n+b+1 := by omega
  rw [ha,hb] at he
  rw [he]
  calc
    _ = (qfactorial q (n+a)*qfactorial q (n+b)/(qfactorial q (a+1)*qfactorial q (b+1)))*
        (qnum q n/(qfactorial q n*qfactorial q n))*qnum q ((a+1)+(b+1)+n) := by ring
    _ = _ := by
      rw [qnum_factorial_ratio q hq n hn]
      unfold mixedWeylDimension
      have ha' : a+1+n-1=n+a := by omega
      have hb' : b+1+n-1=n+b := by omega
      rw [ha',hb']
      ring

end AMSPhysical

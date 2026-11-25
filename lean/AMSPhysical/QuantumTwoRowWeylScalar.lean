import QuantumMixedWeylScalar

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def twoRowWeylDimension (q : ℝ) (n a b : ℕ) : ℝ :=
  qnum q (a+1)*qfactorial q (a+b+n)*qfactorial q (b+n-1)/
    (qfactorial q (a+b+1)*qfactorial q b*qfactorial q n*qfactorial q (n-1))

theorem qInteger_determinant_product (q : ℝ) (hq : q≠0) (x y n : ℤ) :
    qInteger q x*qInteger q (y+n)-qInteger q (x+n)*qInteger q y=
      qInteger q n*qInteger q (x-y) := by
  have hx:=qInteger_add q hq x n
  have hy:=qInteger_add q hq y n
  have hd:=qInteger_add q hq x (-y)
  rw [qInteger_neg,neg_neg] at hd
  rw [show x+ -y=x-y from by ring] at hd
  rw [hx,hy]
  linear_combination -(qInteger q n)*hd

theorem qnum_determinant_product (q : ℝ) (hq : 0<q) (hq1 : q≠1) (x y n : ℕ) (hxy : y≤x) :
    qnum q x*qnum q (y+n)-qnum q (x+n)*qnum q y=qnum q n*qnum q (x-y) := by
  simpa only [qnum_eq_qInteger q hq hq1,Nat.cast_add,Int.natCast_sub hxy] using
    qInteger_determinant_product q (ne_of_gt hq) (x:ℤ) (y:ℤ) (n:ℤ)

theorem twoRowWeylDimension_right_zero (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (a : ℕ) :
    twoRowWeylDimension q n a 0=symmetricQuantumDimension q n a := by
  unfold twoRowWeylDimension symmetricQuantumDimension
  simp only [Nat.add_zero,Nat.zero_add,qfactorial_zero,mul_one]
  rw [qfactorial_succ q a]
  field_simp [qfactorial_ne_zero q hq a,qfactorial_ne_zero q hq n,qfactorial_ne_zero q hq (n-1),
    ne_of_gt (qnum_pos q hq (a+1) (by omega))]
  rw [Nat.add_comm a n]

theorem twoRowWeylDimension_succ_difference (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) :
    symmetricQuantumDimension q n (a+b+1)*symmetricQuantumDimension q n (b+1)-
      symmetricQuantumDimension q n (a+b+2)*symmetricQuantumDimension q n b=
      twoRowWeylDimension q n a (b+1) := by
  have hCross:=qnum_determinant_product q hq hq1 (a+b+2) (b+1) n (by omega)
  rw [show a+b+2-(b+1)=a+1 from by omega] at hCross
  have hFactor :
    symmetricQuantumDimension q n (a+b+1)*symmetricQuantumDimension q n (b+1)-
      symmetricQuantumDimension q n (a+b+2)*symmetricQuantumDimension q n b=
    (qfactorial q (n+(a+b+1))*qfactorial q (n+b)/
      (qfactorial q n*qfactorial q n*qfactorial q (a+b+2)*qfactorial q (b+1)))*
      (qnum q (a+b+2)*qnum q (b+1+n)-qnum q (a+b+2+n)*qnum q (b+1)) := by
    unfold symmetricQuantumDimension
    rw [show n+(b+1)=n+b+1 from by omega,qfactorial_succ q (n+b)]
    rw [show n+(a+b+2)=(n+(a+b+1))+1 from by omega,qfactorial_succ q (n+(a+b+1))]
    rw [show a+b+2=(a+b+1)+1 from by omega,qfactorial_succ q (a+b+1),qfactorial_succ q b]
    rw [show b+1+n=n+b+1 from by omega,show a+b+1+1+n=n+(a+b+1)+1 from by omega]
    field_simp [qfactorial_ne_zero q hq n,qfactorial_ne_zero q hq (a+b+1),qfactorial_ne_zero q hq b,
      ne_of_gt (qnum_pos q hq (a+b+1+1) (by omega)),ne_of_gt (qnum_pos q hq (b+1) (by omega))]
  rw [hFactor,hCross]
  calc
    _ = (qfactorial q (n+(a+b+1))*qfactorial q (n+b)/
      (qfactorial q (a+b+2)*qfactorial q (b+1)))*
      (qnum q n/(qfactorial q n*qfactorial q n))*qnum q (a+1) := by ring
    _ = _ := by
      rw [qnum_factorial_ratio q hq n hn]
      unfold twoRowWeylDimension
      rw [show a+(b+1)+n=n+(a+b+1) from by omega,
        show b+1+n-1=n+b from by omega,show a+(b+1)+1=a+b+2 from by omega]
      ring

end AMSPhysical
#print axioms AMSPhysical.twoRowWeylDimension_succ_difference

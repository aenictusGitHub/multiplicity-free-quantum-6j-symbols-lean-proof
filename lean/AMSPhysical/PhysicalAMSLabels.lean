import PhysicalRacahKernel
import QuantumRacahClosedFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem physicalAMS_offsets (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    AMSGeneral.offsets 0 false (l:ℤ) m n H (coupledLabel l m p.val.1) (coupledLabel m n a.1)=
      physicalRacahOffsets a.1.val p.val.1.val (l+a.1.val-leftHighestDefect l m n H)
        (n-p.val.2.val) (m-p.val.1.val) p.val.2.val := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hi := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hu := channel_left_bound m n a.1
  have hun := channel_right_bound m n a.1
  have hp := leftTotalLabel_defect l m n p.val
  rw [p.property] at hp
  have hdef := fixedLeftHighest_defect l m n H p
  have hadm := rightHighest_spinRacah_admissible l m n H a hH
  have hroot := hadm.rootFirst
  apply AMSGeneral.Offsets.ext <;>
    simp only [AMSGeneral.offsets,physicalRacahOffsets,Bool.false_eq_true,if_false,
      add_zero,coupledLabel_cast l m p.val.1.val hl hm,coupledLabel_cast m n a.1.val hu hun] <;> omega

theorem physicalAMS_rho (l m n H : ℕ) (p : FixedLeftHighest l m n H) :
    AMSGeneral.rho (l:ℤ) m n H=((l+m+n-leftHighestDefect l m n H:ℕ):ℤ) := by
  have hp := leftTotalLabel_defect l m n p.val
  rw [p.property] at hp
  have hd := fixedLeftHighest_defect l m n H p
  unfold AMSGeneral.rho
  omega

/-- Exact identification of the independently derived rank-two sum with AMS's
kernel, using the physical six labels, including the global sign. -/
theorem spinRacahFactorialSum_AMS_kernel (q : ℝ) (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    AMSGeneral.kernel (quantumFactorialInt q) 0 false (l:ℤ) m n H
      (coupledLabel l m p.val.1) (coupledLabel m n a.1)=
      (-1:ℝ)^(l+m+n-leftHighestDefect l m n H)*
        spinRacahFactorialSum q l m n (leftHighestDefect l m n H) a.1.val p.val.1.val p.val.2.val := by
  have hadm := rightHighest_spinRacah_admissible l m n H a hH
  have hsum := hadm.rootSecond
  have hT : a.1.val≤l+m+n-leftHighestDefect l m n H+1 := by omega
  unfold AMSGeneral.kernel
  simp only [Nat.cast_zero,add_zero]
  rw [physicalAMS_rho l m n H p,physicalAMS_offsets l m n H p a hH]
  have hh := factorialRacahSum_AMS_series q a.1.val p.val.1.val
    (l+a.1.val-leftHighestDefect l m n H) (n-p.val.2.val) (m-p.val.1.val) p.val.2.val
    (l+m+n-leftHighestDefect l m n H+1) (l+m+n-leftHighestDefect l m n H) hT
  simpa only [Nat.cast_add,Nat.cast_one,spinRacahFactorialSum] using hh

/-- Actual physical Uq(sl2) recoupling is identified with the exact AMS scalar
kernel, with a closed positive prefactor and a proved global sign. This is a
rank-two theorem; it makes no arbitrary-rank quantum-group assumption. -/
theorem physical_rank_two_AMS_kernel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n H : ℕ) (first : FixedLeftHighest l m n H)
    (hb : first.val.1.val=0 ∨ first.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) (p : FixedLeftHighest l m n H) :
    quantumRacahMatrix q hq hq1 l m n p.val a=
      (-1:ℝ)^(l+m+n-leftHighestDefect l m n H)*physicalRacahClosedPrefactor q l m n H first p a*
        AMSGeneral.kernel (quantumFactorialInt q) 0 false (l:ℤ) m n H
          (coupledLabel l m p.val.1) (coupledLabel m n a.1) := by
  rw [quantumRacahMatrix_closed_factorial_sum q hq hq1 l m n H first hb a hH p,
    spinRacahFactorialSum_AMS_kernel q l m n H p a hH]
  have hs := AMSGeneral.sign_square (𝕂:=ℝ) (l+m+n-leftHighestDefect l m n H)
  linear_combination -(physicalRacahClosedPrefactor q l m n H first p a*
    spinRacahFactorialSum q l m n (leftHighestDefect l m n H) a.1.val p.val.1.val p.val.2.val)*hs

end AMSPhysical

#print axioms AMSPhysical.physical_rank_two_AMS_kernel

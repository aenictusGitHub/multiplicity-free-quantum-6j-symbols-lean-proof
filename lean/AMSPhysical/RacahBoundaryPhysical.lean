import RacahBoundarySquares
import RacahRowNormalization
import RacahSingleTerm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
noncomputable section
namespace AMSPhysical

theorem couplingNormClosed_zero (q : ℝ) (hq : 0<q) (a b : ℕ) : couplingNormClosed q a b 0=1 := by
  unfold couplingNormClosed
  simp only [Nat.cast_zero,mul_zero,zero_mul,zpow_zero,qfactorial_zero,one_mul,Nat.add_zero]
  field_simp [qfactorial_ne_zero q hq]

theorem boundaryRacahNormalization_sq (q : ℝ) (hq : 0<q) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) :
    (boundaryRacahNormalization q l m n p a)^2=
      (couplingNormClosed q (l-p.1.val) (m-p.1.val) p.1.val*
        couplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val)/
      (couplingNormClosed q (m-a.1.val) (n-a.1.val) a.1.val*
        couplingNormClosed q (l-a.2.val) (coupledLabel m n a.1-a.2.val) a.2.val) := by
  unfold boundaryRacahNormalization
  simp only [div_pow,mul_pow,inv_pow,
    Real.sq_sqrt (le_of_lt (couplingNormClosed_pos q hq (l-a.2.val) (coupledLabel m n a.1-a.2.val) a.2.val)),
    Real.sq_sqrt (le_of_lt (couplingNormClosed_pos q hq (m-a.1.val) (n-a.1.val) a.1.val)),
    Real.sq_sqrt (le_of_lt (couplingNormClosed_pos q hq (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val)),
    Real.sq_sqrt (le_of_lt (couplingNormClosed_pos q hq (l-p.1.val) (m-p.1.val) p.1.val)),
    div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

/-- At each extremal row the physical normalization square equals the
standard triangle normalization square, times its single factorial summand. -/
theorem physical_boundary_triangle_square (q : ℝ) (hq : 0<q) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (hb : p.val.1.val=0 ∨ p.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    (boundaryRacahNormalization q l m n p.val a*boundaryRacahRaw q l m n p.val a)^2=
      leftRacahTriangleWeight q l m n p.val*rightRacahTriangleWeight q l m n a*
        (spinRacahFactorialSum q l m n (leftHighestDefect l m n H) a.1.val p.val.1.val p.val.2.val)^2 := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hi := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hu := channel_left_bound m n a.1
  have hun := channel_right_bound m n a.1
  have hv := channel_left_bound l (coupledLabel m n a.1) a.2
  have hvj := channel_right_bound l (coupledLabel m n a.1) a.2
  have hd := fixedLeftHighest_defect l m n H p
  have hL := leftTotalLabel_defect l m n p.val
  have hR := rightTotalLabel_defect l m n a
  rw [p.property] at hL
  rw [hH] at hR
  have hdef : a.1.val+a.2.val=p.val.1.val+p.val.2.val := by omega
  have hli : coupledLabel l m p.val.1+2*p.val.1.val=l+m := by unfold coupledLabel;omega
  have hrj : coupledLabel m n a.1+2*a.1.val=m+n := by unfold coupledLabel;omega
  have hM : a.1.val≤m-p.val.1.val := by rcases hb with hr | hs <;> omega
  have hS : a.1.val≤p.val.2.val := by rcases hb with hr | hs <;> omega
  have hzero : p.val.1.val=0 ∨ n-p.val.2.val=0 := by omega
  rw [mul_pow,boundaryRacahNormalization_sq q hq]
  unfold spinRacahFactorialSum
  rw [factorialRacahSum_single q _ _ _ _ _ _ _ hM hS hzero]
  by_cases hr : p.val.1.val=0
  · unfold boundaryRacahRaw
    rw [if_pos hr]
    have hN : couplingNormClosed q (l-p.val.1.val) (m-p.val.1.val) p.val.1.val=1 := by
      simpa only [hr,Nat.sub_zero] using couplingNormClosed_zero q hq l m
    rw [hN,one_mul]
    have hc := racah_first_boundary_square q hq (l-a.2.val) (n-p.val.2.val) (m-a.1.val) a.1.val a.2.val
    unfold boundaryFirstLeftWeight boundaryFirstRightWeight boundaryFirstKernel at hc
    unfold leftRacahTriangleWeight rightRacahTriangleWeight triangleChannelWeight zeroRacahTerm
    simp only [hr,Nat.sub_zero,qfactorial_zero,one_mul,mul_one]
    simp only [coupledLabel,Nat.mul_zero,Nat.sub_zero]
    convert hc using 1 <;> repeat' first | rfl | omega | congr 1
  · have hs : p.val.2.val=n := hb.resolve_left hr
    unfold boundaryRacahRaw
    rw [if_neg hr]
    have hc := racah_last_boundary_square q hq (l-a.2.val) (m-p.val.1.val-a.1.val) (n-a.1.val) a.1.val p.val.1.val
    unfold boundaryLastLeftWeight boundaryLastRightWeight boundaryLastKernel at hc
    unfold leftRacahTriangleWeight rightRacahTriangleWeight triangleChannelWeight zeroRacahTerm
    simp only [hs,Nat.sub_self,qfactorial_zero,one_mul,mul_one]
    simp only [coupledLabel,Nat.mul_zero,Nat.sub_zero]
    convert hc using 1 <;> repeat' first | rfl | omega | congr 1

end AMSPhysical

#print axioms AMSPhysical.physical_boundary_triangle_square

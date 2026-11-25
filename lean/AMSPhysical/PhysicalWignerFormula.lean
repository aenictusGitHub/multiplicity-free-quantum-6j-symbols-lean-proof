import PhysicalRacahNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

/-- Four triangle factors in the conventional quantum 6j normalization. -/
def wignerTrianglePrefactor (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n)
    (a : RightHighestPath l m n) : ℝ :=
  Real.sqrt (triangleChannelWeight q l m p.1.val*
    triangleChannelWeight q (coupledLabel l m p.1) n p.2.val*
    triangleChannelWeight q m n a.1.val*triangleChannelWeight q l (coupledLabel m n a.1) a.2.val)

/-- A signed, dimension-normalized physical 6j symbol, defined from actual
isometric coupling-tree overlaps rather than from any candidate factorial sum. -/
def physicalQuantumWigner6j (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) : ℝ :=
  (-1:ℝ)^(l+m+n-leftHighestDefect l m n H)*quantumRacahMatrix q hq hq1 l m n p.val a/
    Real.sqrt (qnum q (coupledLabel l m p.val.1+1)*qnum q (coupledLabel m n a.1+1))

theorem standardRacahPrefactor_dimensions (q : ℝ) (hq : 0<q) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) :
    standardRacahPrefactor q l m n p a=
      Real.sqrt (qnum q (coupledLabel l m p.1+1)*qnum q (coupledLabel m n a.1+1))*
        wignerTrianglePrefactor q l m n p a := by
  unfold standardRacahPrefactor wignerTrianglePrefactor
  rw [← Real.sqrt_mul (le_of_lt (mul_pos (qnum_pos q hq _ (by omega)) (qnum_pos q hq _ (by omega))))]
  congr 1
  unfold leftRacahTriangleWeight rightRacahTriangleWeight
  ring

/-- Full physical rank-two quantum Racah formula in the explicit signed
Wigner convention above, valid for every admissible channel at positive
real q != 1. The seven-denominator sum and normalization are conclusions. -/
theorem physicalQuantumWigner6j_AMS (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (a : RightHighestPath l m n)
    (hH : rightTotalLabel l m n a=H) :
    physicalQuantumWigner6j q hq hq1 l m n H p a=
      wignerTrianglePrefactor q l m n p.val a*
        AMSGeneral.kernel (quantumFactorialInt q) 0 false (l:ℤ) m n H
          (coupledLabel l m p.val.1) (coupledLabel m n a.1) := by
  have hdim : Real.sqrt (qnum q (coupledLabel l m p.val.1+1)*qnum q (coupledLabel m n a.1+1))≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos (qnum_pos q hq _ (by omega)) (qnum_pos q hq _ (by omega))))
  unfold physicalQuantumWigner6j
  rw [physical_rank_two_AMS_standard q hq hq1 l m n H p a hH,
    standardRacahPrefactor_dimensions q hq l m n p.val a]
  have hs := AMSGeneral.sign_square (𝕂:=ℝ) (l+m+n-leftHighestDefect l m n H)
  apply (div_eq_iff hdim).mpr
  linear_combination (Real.sqrt (qnum q (coupledLabel l m p.val.1+1)*qnum q (coupledLabel m n a.1+1))*
    wignerTrianglePrefactor q l m n p.val a*
    AMSGeneral.kernel (quantumFactorialInt q) 0 false (l:ℤ) m n H
      (coupledLabel l m p.val.1) (coupledLabel m n a.1))*hs

end AMSPhysical

#print axioms AMSPhysical.physicalQuantumWigner6j_AMS

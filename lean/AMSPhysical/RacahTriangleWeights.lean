import QuantumLeadingRegular
import QuantumGaugeFactor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def triangleChannelWeight (q : ℝ) (l m r : ℕ) : ℝ :=
  qfactorial q r*qfactorial q (l-r)*qfactorial q (m-r)/qfactorial q (l+m-r+1)

def leftRacahTriangleWeight (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  qnum q (coupledLabel l m p.1+1)*triangleChannelWeight q l m p.1.val*
    triangleChannelWeight q (coupledLabel l m p.1) n p.2.val

def rightRacahTriangleWeight (q : ℝ) (l m n : ℕ) (a : RightHighestPath l m n) : ℝ :=
  qnum q (coupledLabel m n a.1+1)*triangleChannelWeight q m n a.1.val*
    triangleChannelWeight q l (coupledLabel m n a.1) a.2.val

def standardRacahPrefactor (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n)
    (a : RightHighestPath l m n) : ℝ :=
  Real.sqrt (leftRacahTriangleWeight q l m n p*rightRacahTriangleWeight q l m n a)

theorem triangleChannelWeight_pos (q : ℝ) (hq : 0<q) (l m r : ℕ) :
    0<triangleChannelWeight q l m r :=
  div_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (qfactorial_pos q hq _)

theorem leftRacahTriangleWeight_pos (q : ℝ) (hq : 0<q) (l m n : ℕ) (p : LeftHighestPath l m n) :
    0<leftRacahTriangleWeight q l m n p :=
  mul_pos (mul_pos (qnum_pos q hq _ (by omega)) (triangleChannelWeight_pos q hq _ _ _))
    (triangleChannelWeight_pos q hq _ _ _)

theorem rightRacahTriangleWeight_pos (q : ℝ) (hq : 0<q) (l m n : ℕ) (a : RightHighestPath l m n) :
    0<rightRacahTriangleWeight q l m n a :=
  mul_pos (mul_pos (qnum_pos q hq _ (by omega)) (triangleChannelWeight_pos q hq _ _ _))
    (triangleChannelWeight_pos q hq _ _ _)

theorem standardRacahPrefactor_pos (q : ℝ) (hq : 0<q) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) : 0<standardRacahPrefactor q l m n p a :=
  Real.sqrt_pos.mpr (mul_pos (leftRacahTriangleWeight_pos q hq _ _ _ _) (rightRacahTriangleWeight_pos q hq _ _ _ _))

/-- The factorial row normalization has exactly the standard triangle weight.
The variables are nonnegative triangle coordinates, so no boundary division
or truncated integer subtraction is hidden in the identity. -/
theorem racah_row_square_coordinates (q : ℝ) (hq : 0<q)
    (a b c d r s : ℕ) (hi : a+b=c+s) :
    (((Real.sqrt (couplingNormClosed q c d s))⁻¹*(Real.sqrt (couplingNormClosed q a b r))⁻¹)*
      (q^(((d:ℤ)-(b:ℤ)-(s:ℤ))*(r:ℤ)-(r:ℤ)^2)*qfactorial q a*qfactorial q c/qfactorial q (c+s))*
      (qfactorial q r*qfactorial q d*qfactorial q b*qfactorial q s))^2=
    q^(2*((r:ℤ)+(s:ℤ))*((d:ℤ)-(r:ℤ)))*
      qfactorial q (a+r)*qfactorial q (b+r)*qfactorial q (d+s)*qfactorial q (c+d+1)*
      (qnum q (c+s+1)*(qfactorial q r*qfactorial q a*qfactorial q b/qfactorial q (c+s+r+1))*
        (qfactorial q s*qfactorial q c*qfactorial q d/qfactorial q (c+d+s+1))) := by
  have hq0 := ne_of_gt hq
  have hN₁ := couplingNormClosed_pos q hq c d s
  have hN₂ := couplingNormClosed_pos q hq a b r
  have hphase : (q^(((d:ℤ)-(b:ℤ)-(s:ℤ))*(r:ℤ)-(r:ℤ)^2))^2=
      q^(2*((r:ℤ)+(s:ℤ))*((d:ℤ)-(r:ℤ)))*q^(-2*(s:ℤ)*(d:ℤ))*q^(-2*(r:ℤ)*(b:ℤ)) := by
    rw [sq,← zpow_add₀ hq0,← zpow_add₀ hq0,← zpow_add₀ hq0]
    congr 1
    ring
  simp only [mul_pow,div_pow,inv_pow,Real.sq_sqrt (le_of_lt hN₁),Real.sq_sqrt (le_of_lt hN₂)]
  unfold couplingNormClosed
  rw [hi]
  have hF : qfactorial q (c+s+1)=qfactorial q (c+s)*qnum q (c+s+1) := qfactorial_succ q (c+s)
  rw [hF,hphase]
  simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  field_simp [qfactorial_ne_zero q hq,
    ne_of_gt (qnum_pos q hq (c+s+1) (by omega)),
    zpow_ne_zero (-2*(s:ℤ)*(d:ℤ)) hq0,zpow_ne_zero (-2*(r:ℤ)*(b:ℤ)) hq0]

end AMSPhysical

#print axioms AMSPhysical.racah_row_square_coordinates

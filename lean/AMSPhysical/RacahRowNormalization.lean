import RacahTriangleWeights
import QuantumRacahClosedFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def racahRowCoefficient (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  qfactorial q p.1.val*qfactorial q (n-p.2.val)*qfactorial q (m-p.1.val)*qfactorial q p.2.val

def racahColumnCoefficient (q : ℝ) (l m n R u : ℕ) : ℝ :=
  qfactorial q u*qfactorial q (l+u-R)*qfactorial q (m-u)*qfactorial q (R-u)/
    (qfactorial q (l+m+n-R+1)*qfactorial q m*qfactorial q R)

def regularRacahRow (q : ℝ) (l m n R : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  regularProjectedLeading q l m n p*projectedGaugeFactor q l m n R p*racahRowCoefficient q l m n p

def racahGlobalRowConstant (q : ℝ) (l m n H : ℕ) : ℝ :=
  q^(2*(leftHighestDefect l m n H:ℤ)*((n:ℤ)-(leftHighestDefect l m n H:ℤ)))*
    qfactorial q l*qfactorial q m*qfactorial q n*qfactorial q (H+1)

def physicalRacahColumnCoefficient (q : ℝ) (l m n H : ℕ) (first : FixedLeftHighest l m n H)
    (a : RightHighestPath l m n) : ℝ :=
  (boundaryRacahNormalization q l m n first.val a*boundaryRacahRaw q l m n first.val a/
    spinRacahEndpointFactorial q m n (leftHighestDefect l m n H) a.1.val)*
    racahColumnCoefficient q l m n (leftHighestDefect l m n H) a.1.val/
      (regularProjectedLeading q l m n first.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) first.val)

theorem spinRacahConstant_row_column (q : ℝ) (l m n R u : ℕ) (p : LeftHighestPath l m n) :
    spinRacahFactorialConstant q l m n R u p.1.val p.2.val=
      racahRowCoefficient q l m n p*racahColumnCoefficient q l m n R u := by
  unfold spinRacahFactorialConstant searsFactorialConstant racahRowCoefficient racahColumnCoefficient
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem regularRacahRow_square (q : ℝ) (hq : 0<q) (l m n H : ℕ) (p : FixedLeftHighest l m n H) :
    (regularRacahRow q l m n (leftHighestDefect l m n H) p.val)^2=
      racahGlobalRowConstant q l m n H*leftRacahTriangleWeight q l m n p.val := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hs := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hd := fixedLeftHighest_defect l m n H p
  have htot := leftTotalLabel_defect l m n p.val
  rw [p.property] at htot
  have hlabel : coupledLabel l m p.val.1+2*p.val.1.val=l+m := by unfold coupledLabel;omega
  have hi : (l-p.val.1.val)+(m-p.val.1.val)=
      (coupledLabel l m p.val.1-p.val.2.val)+p.val.2.val := by omega
  have hE : (((n-p.val.2.val:ℕ):ℤ)-((m-p.val.1.val:ℕ):ℤ)-(p.val.2.val:ℤ))*(p.val.1.val:ℤ)-
      (p.val.1.val:ℤ)^2=quantumGaugeExponent m n (leftHighestDefect l m n H) p.val.1.val := by
    simp only [Nat.cast_sub hn,Nat.cast_sub hm,quantumGaugeExponent]
    have hR : (leftHighestDefect l m n H:ℤ)=(p.val.1.val:ℤ)+(p.val.2.val:ℤ) := by omega
    rw [hR]
    ring
  have hphase : 2*((p.val.1.val:ℤ)+(p.val.2.val:ℤ))*(((n-p.val.2.val:ℕ):ℤ)-(p.val.1.val:ℤ))=
      2*(leftHighestDefect l m n H:ℤ)*((n:ℤ)-(leftHighestDefect l m n H:ℤ)) := by
    rw [Nat.cast_sub hn]
    have hR : (leftHighestDefect l m n H:ℤ)=(p.val.1.val:ℤ)+(p.val.2.val:ℤ) := by omega
    rw [hR]
    ring
  have hden₁ : (coupledLabel l m p.val.1-p.val.2.val)+p.val.2.val+p.val.1.val+1=l+m-p.val.1.val+1 := by omega
  have hden₂ : (coupledLabel l m p.val.1-p.val.2.val)+(n-p.val.2.val)+p.val.2.val+1=
      coupledLabel l m p.val.1+n-p.val.2.val+1 := by omega
  have hH : (coupledLabel l m p.val.1-p.val.2.val)+(n-p.val.2.val)=H := by omega
  have hc := racah_row_square_coordinates q hq (l-p.val.1.val) (m-p.val.1.val)
    (coupledLabel l m p.val.1-p.val.2.val) (n-p.val.2.val) p.val.1.val p.val.2.val hi
  rw [hE,hphase,hden₁,hden₂,hH,Nat.sub_add_cancel hl,Nat.sub_add_cancel hm,Nat.sub_add_cancel hn,
    Nat.sub_add_cancel hs] at hc
  simpa only [regularRacahRow,regularProjectedLeading,projectedGaugeFactor,racahRowCoefficient,
    racahGlobalRowConstant,leftRacahTriangleWeight,triangleChannelWeight,mul_assoc] using hc

theorem physicalRacahPrefactor_row_separated (q : ℝ) (l m n H : ℕ)
    (first p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) :
    physicalRacahClosedPrefactor q l m n H first p a=
      physicalRacahColumnCoefficient q l m n H first a*
        regularRacahRow q l m n (leftHighestDefect l m n H) p.val := by
  unfold physicalRacahClosedPrefactor
  rw [spinRacahConstant_row_column]
  unfold physicalRacahColumnCoefficient regularRacahRow
  ring

theorem physicalRacahPrefactor_square_ratio (q : ℝ) (hq : 0<q) (l m n H : ℕ)
    (first p : FixedLeftHighest l m n H) (a : RightHighestPath l m n) :
    (physicalRacahClosedPrefactor q l m n H first p a)^2*leftRacahTriangleWeight q l m n first.val=
      (physicalRacahClosedPrefactor q l m n H first first a)^2*leftRacahTriangleWeight q l m n p.val := by
  rw [physicalRacahPrefactor_row_separated q l m n H first p a,
    physicalRacahPrefactor_row_separated q l m n H first first a,mul_pow,mul_pow,
    regularRacahRow_square q hq l m n H p,regularRacahRow_square q hq l m n H first]
  ring

end AMSPhysical

#print axioms AMSPhysical.regularRacahRow_square
#print axioms AMSPhysical.physicalRacahPrefactor_square_ratio

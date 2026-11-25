import SpinRacahGauge
import QuantumPathNormNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def quantumGaugeExponent (m n R r : ℕ) : ℤ :=
  ((n:ℤ)-(m:ℤ)-2*(R:ℤ))*(r:ℤ)+2*(r:ℤ)^2

def projectedGaugeFactor (q : ℝ) (l m n R : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  q^(quantumGaugeExponent m n R p.1.val)*qfactorial q (l-p.1.val)*
    qfactorial q (coupledLabel l m p.1-p.2.val)/qfactorial q (coupledLabel l m p.1)

theorem projectedGaugeFactor_pos (q : ℝ) (hq : 0<q) (l m n R : ℕ) (p : LeftHighestPath l m n) :
    0<projectedGaugeFactor q l m n R p := by
  exact div_pos (mul_pos (mul_pos (zpow_pos hq _) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (qfactorial_pos q hq _)

theorem sl2RacahDeath_qnum (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) (p : LeftHighestPath l m n) :
    sl2RacahDeath q l m n p.1.val p.2.val=
      (q-q⁻¹)^2*qnum q p.1.val*qnum q (n-p.2.val)*qnum q (l-p.1.val+1)*
        qnum q (coupledLabel l m p.1-p.2.val+1)/
          (qnum q (coupledLabel l m p.1+1)*qnum q (coupledLabel l m p.1+2)) := by
  have hl := channel_left_bound l m p.1
  have hm := channel_right_bound l m p.1
  have hs := channel_left_bound (coupledLabel l m p.1) n p.2
  have hn := channel_right_bound (coupledLabel l m p.1) n p.2
  unfold sl2RacahDeath
  simp only [qnum_eq_qInteger q hq hq1,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Nat.cast_sub hl,Nat.cast_sub hn,Nat.cast_sub hs,coupledLabel_cast l m p.1.val hl hm]

theorem quantumGaugeExponent_neighbor (l m n H : ℕ) (p v : FixedLeftHighest l m n H)
    (hv : v.val.1.val+1=p.val.1.val) :
    quantumGaugeExponent m n (leftHighestDefect l m n H) p.val.1.val=
      (n:ℤ)-(m:ℤ)+2*(p.val.1.val:ℤ)-2*(p.val.2.val:ℤ)-2+
        quantumGaugeExponent m n (leftHighestDefect l m n H) v.val.1.val := by
  have hd := fixedLeftHighest_defect l m n H p
  have hR : (leftHighestDefect l m n H:ℤ)=(p.val.1.val:ℤ)+(p.val.2.val:ℤ) := by omega
  have hr : (v.val.1.val:ℤ)=(p.val.1.val:ℤ)-1 := by omega
  unfold quantumGaugeExponent
  rw [hR,hr]
  ring

/-- A closed factorial gauge satisfies the independently proved physical
neighbor recurrence. No product over intermediate channels remains. -/
theorem projectedGaugeFactor_neighbor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hv : v.val.1.val+1=p.val.1.val) :
    sl2RacahDeath q l m n p.val.1.val p.val.2.val*
      projectedGaugeFactor q l m n (leftHighestDefect l m n H) p.val=
      casimirLowerStep q m n p.val.1.val p.val.2.val*
        projectedGaugeFactor q l m n (leftHighestDefect l m n H) v.val := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hs := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hvs := fixedLeftHighest_previous_second l m n H p v hv
  have hvi : coupledLabel l m v.val.1=coupledLabel l m p.val.1+2 := by unfold coupledLabel;omega
  have hvl : l-v.val.1.val=l-p.val.1.val+1 := by omega
  have hvis : coupledLabel l m v.val.1-v.val.2.val=coupledLabel l m p.val.1-p.val.2.val+1 := by omega
  have hphase : q^(quantumGaugeExponent m n (leftHighestDefect l m n H) p.val.1.val)=
      q^((n:ℤ)-(m:ℤ)+2*(p.val.1.val:ℤ)-2*(p.val.2.val:ℤ)-2)*
        q^(quantumGaugeExponent m n (leftHighestDefect l m n H) v.val.1.val) := by
    rw [← zpow_add₀ (ne_of_gt hq),quantumGaugeExponent_neighbor l m n H p v hv]
  rw [sl2RacahDeath_qnum q hq hq1,casimirLowerStep_closed q hq hq1 m n p.val.1.val p.val.2.val hn]
  unfold projectedGaugeFactor
  rw [hvl,hvis,hvi,hphase,qfactorial_succ q (l-p.val.1.val),
    qfactorial_succ q (coupledLabel l m p.val.1-p.val.2.val)]
  have hFi : qfactorial q (coupledLabel l m p.val.1+2)=
      qfactorial q (coupledLabel l m p.val.1)*qnum q (coupledLabel l m p.val.1+1)*
        qnum q (coupledLabel l m p.val.1+2) := by
    rw [qfactorial_succ q (coupledLabel l m p.val.1+1),qfactorial_succ q (coupledLabel l m p.val.1)]
  rw [hFi]
  field_simp [qfactorial_ne_zero q hq (coupledLabel l m p.val.1),
    ne_of_gt (qnum_pos q hq (coupledLabel l m p.val.1+1) (by omega)),
    ne_of_gt (qnum_pos q hq (coupledLabel l m p.val.1+2) (by omega))]

end AMSPhysical

#print axioms AMSPhysical.projectedGaugeFactor_neighbor

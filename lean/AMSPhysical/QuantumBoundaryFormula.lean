import QuantumBoundaryRecoupling
import QuantumClebschFirstFormula
import QuantumClebschAnalytic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def boundaryRacahRaw (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) (a : RightHighestPath l m n) : ℝ :=
  if p.1.val=0 then
    q^(-(a.2.val:ℤ)*(m:ℤ))*qfactorial q (n-a.1.val)*qfactorial q (coupledLabel m n a.1-a.2.val)/
      (qfactorial q (coupledLabel m n a.1)*qfactorial q (n-p.2.val))
  else
    q^((n:ℤ)*(p.1.val:ℤ)-(m:ℤ)*((n-a.1.val:ℕ):ℤ))*qfactorial q a.2.val*qfactorial q (m-a.1.val)/
      (qfactorial q (coupledLabel m n a.1)*qfactorial q p.1.val)

def boundaryRacahNormalization (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) (a : RightHighestPath l m n) : ℝ :=
  (Real.sqrt (couplingNormClosed q (l-a.2.val) (coupledLabel m n a.1-a.2.val) a.2.val))⁻¹*
    (Real.sqrt (couplingNormClosed q (m-a.1.val) (n-a.1.val) a.1.val))⁻¹/
      ((Real.sqrt (couplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val))⁻¹*
        (Real.sqrt (couplingNormClosed q (l-p.1.val) (m-p.1.val) p.1.val))⁻¹)

/-- A closed factorial expression for every admissible extremal left row of the physical matrix. -/
theorem quantumRacah_boundary_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (hbound : p.val.1.val=0 ∨ p.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    quantumRacahMatrix q hq hq1 l m n p.val a=
      boundaryRacahNormalization q l m n p.val a*boundaryRacahRaw q l m n p.val a := by
  have he := quantumRacah_boundary_projection q hq hq1 l m n H p hbound a hH
  have hn := ne_of_gt (projectedLeftLeading_pos q hq l m n p.val)
  have hf := (eq_div_iff hn).mpr he
  have hp := leftTotalLabel_defect l m n p.val
  have ha := rightTotalLabel_defect l m n a
  rw [p.property] at hp
  rw [hH] at ha
  have hdef : a.1.val+a.2.val=p.val.1.val+p.val.2.val := by omega
  rw [hf]
  by_cases hr : p.val.1.val=0
  · have hs := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
    have hc := standardClebschCoefficient_first_closed q hq hq1 m n a.1
      (rightPathWeightIndex l m n a) p.val.2.val (by change p.val.2.val=a.1.val+a.2.val;omega) hs
    have hc' : standardClebschCoefficient q hq hq1 m n a.1 (rightPathWeightIndex l m n a)
        p.val.1.val p.val.2.val=
        (Real.sqrt (quantumHighestNorm q m n a.1))⁻¹*q^(-(a.2.val:ℤ)*(m:ℤ))*
          qfactorial q (n-a.1.val)*qfactorial q (coupledLabel m n a.1-a.2.val)/
            (qfactorial q (coupledLabel m n a.1)*qfactorial q (n-p.val.2.val)) := by
      simpa only [hr,Nat.cast_zero,rightPathWeightIndex] using hc
    rw [hc']
    unfold boundaryRacahRaw boundaryRacahNormalization projectedLeftLeading
    rw [if_pos hr]
    simp only [quantumHighestNorm_closed q hq hq1,rightPathWeightIndex]
    ring
  · have hs : p.val.2.val=n := hbound.resolve_left hr
    have hu := channel_right_bound m n a.1
    have hc := standardClebschCoefficient_last_closed q hq hq1 m n a.1
      (rightPathWeightIndex l m n a) p.val.1.val
      (by change a.2.val=(n-a.1.val)+p.val.1.val;omega)
    have hc' : standardClebschCoefficient q hq hq1 m n a.1 (rightPathWeightIndex l m n a)
        p.val.1.val p.val.2.val=
        (Real.sqrt (quantumHighestNorm q m n a.1))⁻¹*
          q^((n:ℤ)*(p.val.1.val:ℤ)-(m:ℤ)*((n-a.1.val:ℕ):ℤ))*
          qfactorial q a.2.val*qfactorial q (m-a.1.val)/
            (qfactorial q (coupledLabel m n a.1)*qfactorial q p.val.1.val) := by
      simpa only [hs,rightPathWeightIndex] using hc
    rw [hc']
    unfold boundaryRacahRaw boundaryRacahNormalization projectedLeftLeading
    rw [if_neg hr]
    simp only [quantumHighestNorm_closed q hq hq1,rightPathWeightIndex]
    ring

theorem boundaryRacahRaw_pos (q : ℝ) (hq : 0<q) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) : 0<boundaryRacahRaw q l m n p a := by
  unfold boundaryRacahRaw
  split <;> exact div_pos (mul_pos (mul_pos (zpow_pos hq _) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))

theorem boundaryRacahNormalization_pos (q : ℝ) (hq : 0<q) (l m n : ℕ)
    (p : LeftHighestPath l m n) (a : RightHighestPath l m n) : 0<boundaryRacahNormalization q l m n p a := by
  unfold boundaryRacahNormalization
  exact div_pos
    (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _)))
      (inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _))))
    (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _)))
      (inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _))))

/-- The sign of the extremal physical row is proved, not inferred from its square. -/
theorem quantumRacah_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) (hbound : p.val.1.val=0 ∨ p.val.2.val=n)
    (a : RightHighestPath l m n) (hH : rightTotalLabel l m n a=H) :
    0<quantumRacahMatrix q hq hq1 l m n p.val a := by
  rw [quantumRacah_boundary_factorial q hq hq1 l m n H p hbound a hH]
  exact mul_pos (boundaryRacahNormalization_pos q hq l m n p.val a) (boundaryRacahRaw_pos q hq l m n p.val a)

end AMSPhysical

#print axioms AMSPhysical.quantumRacah_boundary_factorial
#print axioms AMSPhysical.quantumRacah_boundary_pos

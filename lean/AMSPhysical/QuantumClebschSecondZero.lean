import QuantumClebschFirstFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem clebschSingleSum_second_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℤ) (r a : ℕ) :
    clebschSingleSum q l m r a ((r:ℤ)+(a:ℤ)) =
      (-1:ℝ)^r*q^(couplingExponent m r r)*qFalling q (l-(r:ℤ)) a := by
  classical
  unfold clebschSingleSum
  rw [Finset.sum_eq_single r]
  · have ha : DescendantAdmissible a r ((r:ℤ)+(a:ℤ)) := by
      unfold DescendantAdmissible
      constructor <;> omega
    have hi : descendantIndex a r ((r:ℤ)+(a:ℤ))=0 := by
      unfold descendantIndex
      omega
    rw [if_pos ha,hi]
    rw [clebschSingleTerm,couplingCoefficient_factorial q hq hq1 m r r (le_refl _)]
    simp only [gaussianBinomial_zero_right,Nat.cast_zero,zero_mul,neg_zero,zpow_zero,
      mul_one,Nat.sub_zero,qFalling,Nat.sub_self,qfactorial_zero,mul_one]
    rw [mul_div_cancel_right₀ _ (qfactorial_ne_zero q hq r)]
  · intro k hk hkr
    have ha : ¬ DescendantAdmissible a k ((r:ℤ)+(a:ℤ)) := by
      intro hadm
      have hk' := Finset.mem_range.mp hk
      have ha' := hadm.1
      omega
    rw [if_neg ha]
  · intro hr
    exact (hr (Finset.mem_range.mpr (by omega))).elim

/-- The second-input highest boundary has the fixed sign (-1)^r.
All remaining factors are strictly positive for positive q. -/
theorem standardClebschCoefficient_second_zero_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m : ℕ) (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1))
    (ha : r.val+a.val≤l) :
    standardClebschCoefficient q hq hq1 l m r a ((r.val:ℤ)+(a.val:ℤ)) 0 =
      (-1:ℝ)^r.val*((Real.sqrt (quantumHighestNorm q l m r))⁻¹ *
        q^(couplingExponent (m:ℤ) r.val r.val)*
        qfactorial q (coupledLabel l m r-a.val)*qfactorial q (l-r.val) /
          (qfactorial q (coupledLabel l m r)*qfactorial q (l-r.val-a.val))) := by
  rw [standardClebschCoefficient_singleSum q hq hq1 l m r a _ 0 (by omega),
    clebschSingleSum_second_zero q hq hq1,← quantumHighestNorm_closed q hq hq1 l m r]
  have hc : (l:ℤ)-(r.val:ℤ)=((l-r.val:ℕ):ℤ) := by
    have hr:=channel_left_bound l m r
    omega
  rw [hc,qFalling_factorial q hq hq1 (coupledLabel l m r) a.val (by have hh:=a.isLt;omega),
    qFalling_factorial q hq hq1 (l-r.val) a.val (by omega)]
  field_simp [qfactorial_ne_zero q hq (coupledLabel l m r),
    qfactorial_ne_zero q hq (coupledLabel l m r-a.val),qfactorial_ne_zero q hq (l-r.val-a.val)]

theorem standardClebschCoefficient_second_zero_signed_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m : ℕ) (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1))
    (ha : r.val+a.val≤l) :
    0 < (-1:ℝ)^r.val*standardClebschCoefficient q hq hq1 l m r a ((r.val:ℤ)+(a.val:ℤ)) 0 := by
  rw [standardClebschCoefficient_second_zero_closed q hq hq1 l m r a ha,← mul_assoc,← mul_pow]
  norm_num only [neg_mul_neg,one_mul,one_pow]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq l m r)))
      (zpow_pos hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))

end AMSPhysical
#print axioms AMSPhysical.standardClebschCoefficient_second_zero_signed_pos

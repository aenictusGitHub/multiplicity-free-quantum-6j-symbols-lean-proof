import PochhammerRatioFactorial
import SpinRacahEndpoints
import SpinRacahScale

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def spinRacahEndpointFactorial (q : ℝ) (m n R u : ℕ) : ℝ :=
  if n≤R then
    qfactorial q n*qfactorial q (m+n-R)*qfactorial q (m-u)*qfactorial q (R-u)/
      (qfactorial q (n-u)*qfactorial q (m+n-R-u)*qfactorial q m*qfactorial q R)
  else 1

theorem spinRacahEndpointFactorial_pos (q : ℝ) (hq : 0<q) (m n R u : ℕ) :
    0<spinRacahEndpointFactorial q m n R u := by
  unfold spinRacahEndpointFactorial
  split
  · exact div_pos
      (mul_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))
        (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
      (mul_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))
        (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
  · norm_num

/-- Explicit positive factorial value of the extremal q-Racah polynomial. -/
theorem spinRacah_lower_endpoint_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n R u : ℕ) (h : SpinRacahAdmissible l m n R u) :
    spinRacahFunction (q^2) l m n R u ((R-n:ℕ):ℤ)=spinRacahEndpointFactorial q m n R u := by
  have hum := h.middle
  have hun := h.last
  have huR := h.defect
  have hsum := h.rootSecond
  unfold spinRacahEndpointFactorial
  by_cases hn : n≤R
  · rw [if_pos hn,spinRacah_lower_endpoint_formula (q^2) (sq_pos_of_pos hq)
      (quantum_square_base_ne_one q hq hq1) l m n R u h hn]
    have ha : (n:ℤ)+1-(u:ℤ)=((n-u:ℕ):ℤ)+1 := by omega
    have hb : (R:ℤ)-(m:ℤ)-(n:ℤ)=-((m+n-R:ℕ):ℤ) := by omega
    have hd : (R:ℤ)+1-(u:ℤ)=((R-u:ℕ):ℤ)+1 := by omega
    rw [ha,hb,hd]
    simp only [square_zpow_even,mul_neg,neg_mul]
    have hh := qPochhammer_balanced_factorial_ratio q hq hq1 (n-u) (m+n-R) m (R-u) u
      (by omega) hum (by omega)
    simpa only [Nat.sub_add_cancel hun,Nat.sub_add_cancel huR] using hh
  · rw [if_neg hn]
    have hz : R-n=0 := by omega
    simp only [spinRacahFunction,hz,Nat.cast_zero,zpow_zero,qRacahSeries_one]

end AMSPhysical

#print axioms AMSPhysical.spinRacah_lower_endpoint_factorial

import SpinRacahEndpointPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem spinRacah_lower_endpoint_formula (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) (hn : n≤R) :
    spinRacahFunction Q l m n R u ((R-n:ℕ):ℤ)=
      qPochhammer Q (Q^((n:ℤ)+1-(u:ℤ))) u*qPochhammer Q (Q^((R:ℤ)-(m:ℤ)-(n:ℤ))) u/
        (qPochhammer Q (Q^(-(m:ℤ))) u*qPochhammer Q (Q^((R:ℤ)+1-(u:ℤ))) u) := by
  have hp := spinRacah_pochhammer_nonzero Q hQ hQ1 l m n R u h
  have hd := spinRacah_product_denominators Q hQ hQ1 l m n R u h
  have hx : Q^((R-n:ℕ):ℤ)=spinRacahA Q n/spinRacahA Q R := by
    rw [spinRacah_B_over_C Q (ne_of_gt hQ)]
    congr 1
    omega
  unfold spinRacahFunction
  rw [hx,qRacahSeries_lower_endpoint Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R) (spinRacahFourth Q l m R) hQ hQ1
    (zpow_ne_zero _ (ne_of_gt hQ)) (zpow_ne_zero _ (ne_of_gt hQ)) (zpow_ne_zero _ (ne_of_gt hQ))
    u hp.2.1 hp.2.2.1 hp.2.2.2 hd.1]
  rw [spinRacah_CN_power Q (ne_of_gt hQ),spinRacah_ABQ_over_C Q (ne_of_gt hQ),
    spinRacahA_mul Q (ne_of_gt hQ),spinRacah_CN_power Q (ne_of_gt hQ)]

theorem spinRacah_lower_endpoint_nonzero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) : spinRacahFunction Q l m n R u ((R-n:ℕ):ℤ)≠0 := by
  by_cases hn : n≤R
  · rw [spinRacah_lower_endpoint_formula Q hQ hQ1 l m n R u h hn]
    have hum := h.middle
    have hun := h.last
    have huR := h.defect
    have hvj := h.rootSecond
    exact div_ne_zero
      (mul_ne_zero (qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inl (by omega)))
        (qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))))
      (mul_ne_zero (qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega)))
        (qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inl (by omega))))
  · have hz : R-n=0 := by omega
    simp only [spinRacahFunction,hz,Nat.cast_zero,zpow_zero,qRacahSeries_one,ne_eq,one_ne_zero,not_false_eq_true]

/-- The first virtual upper value vanishes whenever the physical interval ends at l. -/
theorem spinRacah_virtual_left_zero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) (hR : l<R) :
    spinRacahFunction Q l m n R u ((l:ℤ)+1)=0 := by
  have hp := spinRacah_pochhammer_nonzero Q hQ hQ1 l m n R u h
  have hd := spinRacah_product_denominators Q hQ hQ1 l m n R u h
  unfold spinRacahFunction
  rw [← spinRacah_A_over_CD Q (ne_of_gt hQ) l m R,
    qRacahSeries_upper_A_endpoint Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R) (spinRacahFourth Q l m R) hQ hQ1
      (zpow_ne_zero _ (ne_of_gt hQ)) (zpow_ne_zero _ (ne_of_gt hQ))
      (zpow_ne_zero _ (ne_of_gt hQ)) (zpow_ne_zero _ (ne_of_gt hQ)) u hp.2.1 hp.2.2.1 hp.2.2.2 hd.1]
  have hz : qPochhammer Q (spinRacahFourth Q l m R/(spinRacahA Q m*Q^u)) u=0 := by
    rw [spinRacah_D_over_AN Q (ne_of_gt hQ)]
    have hv := h.rootFirst
    exact qPochhammer_integer_power_zero Q (ne_of_gt hQ) _ u (by omega) (by omega)
  rw [hz,zero_mul,zero_div]

/-- The other virtual upper value vanishes when the physical endpoint is l+m-R. -/
theorem spinRacah_virtual_reflected_zero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) (hR : l<R) :
    spinRacahFunction Q l m n R u ((l:ℤ)+(m:ℤ)-(R:ℤ)+1)=0 := by
  have hp := spinRacah_pochhammer_nonzero Q hQ hQ1 l m n R u h
  have hd := spinRacah_product_denominators Q hQ hQ1 l m n R u h
  unfold spinRacahFunction
  rw [← spinRacah_D_inv Q l m R,qRacahSeries_upper_D_endpoint Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R) (spinRacahFourth Q l m R) hQ hQ1
    (zpow_ne_zero _ (ne_of_gt hQ)) (zpow_ne_zero _ (ne_of_gt hQ)) (zpow_ne_zero _ (ne_of_gt hQ))
    u hp.2.1 hp.2.2.1 hp.2.2.2 hd.2]
  have hz : qPochhammer Q (spinRacahA Q m*Q/spinRacahFourth Q l m R) u=0 := by
    rw [spinRacah_AQ_over_D Q (ne_of_gt hQ)]
    have hv := h.rootFirst
    exact qPochhammer_integer_power_zero Q (ne_of_gt hQ) _ u (by omega) (by omega)
  rw [hz,mul_zero,zero_div]

end AMSPhysical

#print axioms AMSPhysical.spinRacah_lower_endpoint_nonzero
#print axioms AMSPhysical.spinRacah_virtual_left_zero
#print axioms AMSPhysical.spinRacah_virtual_reflected_zero

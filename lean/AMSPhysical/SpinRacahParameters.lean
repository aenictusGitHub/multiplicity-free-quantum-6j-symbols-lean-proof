import IntegerPochhammer

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def spinRacahA (Q : ℝ) (k : ℕ) : ℝ := Q^(-(k:ℤ)-1)
def spinRacahFourth (Q : ℝ) (l m R : ℕ) : ℝ := Q^((R:ℤ)-(l:ℤ)-(m:ℤ)-1)

def spinRacahFunction (Q : ℝ) (l m n R u : ℕ) (r : ℤ) : ℝ :=
  qRacahSeries Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R)
    (spinRacahFourth Q l m R) u (Q^r)

structure SpinRacahAdmissible (l m n R u : ℕ) : Prop where
  middle : u≤m
  last : u≤n
  defect : u≤R
  rootFirst : R≤l+u
  rootSecond : R+u≤m+n

theorem zpow_mul_base (Q : ℝ) (hQ : Q≠0) (a : ℤ) : Q^a*Q=Q^(a+1) := by
  rw [zpow_add₀ hQ,zpow_one]

theorem spinRacahA_mul (Q : ℝ) (hQ : Q≠0) (k : ℕ) : spinRacahA Q k*Q=Q^(-(k:ℤ)) := by
  unfold spinRacahA
  rw [zpow_mul_base Q hQ]
  congr 1
  ring

theorem spinRacahBD_mul (Q : ℝ) (hQ : Q≠0) (l m n R : ℕ) :
    spinRacahA Q n*spinRacahFourth Q l m R*Q=Q^((R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1) := by
  unfold spinRacahA spinRacahFourth
  rw [← zpow_add₀ hQ,zpow_mul_base Q hQ]
  congr 1
  ring

theorem spinRacah_pochhammer_nonzero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) :
    qPochhammer Q Q u≠0 ∧ qPochhammer Q (spinRacahA Q m*Q) u≠0 ∧
      qPochhammer Q (spinRacahA Q n*spinRacahFourth Q l m R*Q) u≠0 ∧
        qPochhammer Q (spinRacahA Q R*Q) u≠0 := by
  rcases h with ⟨hum,hun,huR,hvl,hvj⟩
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [zpow_one] using qPochhammer_integer_power_nonzero Q hQ hQ1 1 u (Or.inl (by norm_num))
  · rw [spinRacahA_mul Q (ne_of_gt hQ)]
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))
  · rw [spinRacahBD_mul Q (ne_of_gt hQ)]
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))
  · rw [spinRacahA_mul Q (ne_of_gt hQ)]
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))

theorem spinRacah_series_regular (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) :
    QRacahSeriesRegular Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R) (spinRacahFourth Q l m R) u := by
  have hp := spinRacah_pochhammer_nonzero Q hQ hQ1 l m n R u h
  exact qRacahSeriesRegular_of_pochhammer Q _ _ _ _ u hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

theorem spinRacah_CN_power (Q : ℝ) (hQ : Q≠0) (R u : ℕ) :
    1/(spinRacahA Q R*Q^u)=Q^((R:ℤ)+1-(u:ℤ)) := by
  unfold spinRacahA
  rw [← zpow_natCast Q u,← zpow_add₀ hQ,one_div,← zpow_neg]
  congr 1
  ring

theorem spinRacah_BDN_power (Q : ℝ) (hQ : Q≠0) (l m n R u : ℕ) :
    1/(spinRacahA Q n*spinRacahFourth Q l m R*Q^u)=Q^((l:ℤ)+(m:ℤ)+(n:ℤ)+2-(R:ℤ)-(u:ℤ)) := by
  unfold spinRacahA spinRacahFourth
  rw [← zpow_natCast Q u,← zpow_add₀ hQ,← zpow_add₀ hQ,one_div,← zpow_neg]
  congr 1
  ring

theorem spinRacah_product_denominators (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u : ℕ)
    (h : SpinRacahAdmissible l m n R u) :
    qPochhammer Q (1/(spinRacahA Q R*Q^u)) u≠0 ∧
      qPochhammer Q (1/(spinRacahA Q n*spinRacahFourth Q l m R*Q^u)) u≠0 := by
  rcases h with ⟨hum,hun,huR,hvl,hvj⟩
  constructor
  · rw [spinRacah_CN_power Q (ne_of_gt hQ)]
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inl (by omega))
  · rw [spinRacah_BDN_power Q (ne_of_gt hQ)]
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inl (by omega))

end AMSPhysical

#print axioms AMSPhysical.spinRacah_pochhammer_nonzero
#print axioms AMSPhysical.spinRacah_series_regular

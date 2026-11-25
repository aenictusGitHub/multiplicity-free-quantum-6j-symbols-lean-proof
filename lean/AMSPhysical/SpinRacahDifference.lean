import SpinRacahParameters
import QRacahRegularizedSeries
import QuantumCoupledStrings

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def spinRacahForward (Q : ℝ) (l m n R : ℕ) (r : ℤ) : ℝ :=
  qRacahB Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R) (spinRacahFourth Q l m R) (Q^r)
def spinRacahBackward (Q : ℝ) (l m n R : ℕ) (r : ℤ) : ℝ :=
  qRacahD Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R) (spinRacahFourth Q l m R) (Q^r)
def spinRacahSpectral (Q : ℝ) (m n u : ℕ) : ℝ :=
  qRacahLambda Q (spinRacahA Q m) (spinRacahA Q n) (Q^u)

theorem one_sub_zpow_nonzero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (a : ℤ) (ha : a≠0) :
    1-Q^a≠0 := by
  intro hz
  have hp : Q^a=Q^(0:ℤ) := by simpa only [zpow_zero] using (sub_eq_zero.mp hz).symm
  exact ha (zpow_right_injective₀ hQ hQ1 hp)

theorem spinRacah_operator_power (Q : ℝ) (hQ : Q≠0) (l m R r k : ℕ) (hl : r≤l) (hm : r≤m) :
    spinRacahA Q R*spinRacahFourth Q l m R*Q^k*(Q^(r:ℤ))^2=
      Q^(-((coupledLabel l m r:ℤ)+2-(k:ℤ))) := by
  unfold spinRacahA spinRacahFourth
  rw [← zpow_add₀ hQ,← zpow_natCast Q k,← zpow_add₀ hQ]
  have ht : (Q^(r:ℤ))^2=Q^((r:ℤ)+(r:ℤ)) := by rw [sq,← zpow_add₀ hQ]
  rw [ht,← zpow_add₀ hQ]
  congr 1
  rw [coupledLabel_cast l m r hl hm]
  ring

/-- The physical-parameter 4phi3 obeys its grid recurrence for all admissible
left channels, including the removable zero-spin singularity. -/
theorem spinRacahFunction_difference (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u r s : ℕ)
    (h : SpinRacahAdmissible l m n R u) (hl : r≤l) (hm : r≤m)
    (hs : s≤coupledLabel l m r) (hR : r+s=R) :
    spinRacahForward Q l m n R r*(spinRacahFunction Q l m n R u ((r:ℤ)+1)-spinRacahFunction Q l m n R u r)+
      spinRacahBackward Q l m n R r*(spinRacahFunction Q l m n R u ((r:ℤ)-1)-spinRacahFunction Q l m n R u r)=
      spinRacahSpectral Q m n u*spinRacahFunction Q l m n R u r := by
  have hq0 := ne_of_gt hQ
  have ht := zpow_ne_zero (r:ℤ) hq0
  have hreg := spinRacah_series_regular Q hQ hQ1 l m n R u h
  have hp0 := spinRacah_operator_power Q hq0 l m R r 0 hl hm
  have hp1 := spinRacah_operator_power Q hq0 l m R r 1 hl hm
  have hp2 := spinRacah_operator_power Q hq0 l m R r 2 hl hm
  have hd0 : 1-spinRacahA Q R*spinRacahFourth Q l m R*(Q^(r:ℤ))^2≠0 := by
    have hh : 1-spinRacahA Q R*spinRacahFourth Q l m R*Q^0*(Q^(r:ℤ))^2≠0 := by
      rw [hp0]
      exact one_sub_zpow_nonzero Q hQ hQ1 _ (by omega)
    simpa only [pow_zero,mul_one] using hh
  have hd1 : 1-spinRacahA Q R*spinRacahFourth Q l m R*Q*(Q^(r:ℤ))^2≠0 := by
    have hh : 1-spinRacahA Q R*spinRacahFourth Q l m R*Q^1*(Q^(r:ℤ))^2≠0 := by
      rw [hp1]
      exact one_sub_zpow_nonzero Q hQ hQ1 _ (by omega)
    simpa only [pow_one] using hh
  have htplus : Q*Q^(r:ℤ)=Q^((r:ℤ)+1) := by rw [zpow_add₀ hq0,zpow_one];ring
  have htminus : Q^(r:ℤ)/Q=Q^((r:ℤ)-1) := by rw [zpow_sub₀ hq0,zpow_one]
  unfold spinRacahForward spinRacahBackward spinRacahSpectral spinRacahFunction
  by_cases hi : coupledLabel l m r=0
  · have hlr : l=r := by unfold coupledLabel at hi;omega
    have hmr : m=r := by unfold coupledLabel at hi;omega
    have hsr : s=0 := by omega
    have hRr : R=r := by omega
    have hC : spinRacahA Q R=spinRacahA Q m := by congr 1;omega
    have hD : spinRacahFourth Q l m R=spinRacahA Q m := by
      unfold spinRacahFourth spinRacahA
      congr 1
      omega
    have hreg' : QRacahSeriesRegular Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q m) (spinRacahA Q m) u := by
      simpa only [hC,hD] using hreg
    have hd0' : 1-(spinRacahA Q m)^2*(Q^(r:ℤ))^2≠0 := by simpa only [hC,hD,pow_two] using hd0
    have hd1' : 1-(spinRacahA Q m)^2*Q*(Q^(r:ℤ))^2≠0 := by simpa only [hC,hD,pow_two] using hd1
    have hdp : 1+spinRacahA Q m*Q*Q^(r:ℤ)≠0 := by
      have hA : 0<spinRacahA Q m := zpow_pos hQ _
      have hp := mul_pos (mul_pos hA hQ) (zpow_pos hQ (r:ℤ))
      exact ne_of_gt (by linarith)
    have he := qRacahSeries_difference_regularized Q (spinRacahA Q m) (spinRacahA Q n) (Q^(r:ℤ))
      hq0 ht u hreg' hd0' hd1' hdp
    simpa only [hC,hD,htplus,htminus] using he
  · have hd2 : 1-spinRacahA Q R*spinRacahFourth Q l m R*Q^2*(Q^(r:ℤ))^2≠0 := by
      rw [hp2]
      exact one_sub_zpow_nonzero Q hQ hQ1 _ (by omega)
    have he := qRacahSeries_difference Q (spinRacahA Q m) (spinRacahA Q n) (spinRacahA Q R)
      (spinRacahFourth Q l m R) (Q^(r:ℤ)) hq0 ht u hreg hd0 hd1 hd2
    simpa only [htplus,htminus] using he

end AMSPhysical

#print axioms AMSPhysical.spinRacahFunction_difference

import SpinRacahChannels
import QuantumNeighborRates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Positive Jacobi normalization, given by a finite product of explicit
quantum-integer factors, independent of physical intertwiner maps. -/
def spinRacahGaugeStep (q : ℝ) (l m n R : ℕ) (r : ℕ) : ℝ :=
  Real.sqrt (sl2RacahDeath q l m n ((r:ℤ)+1) ((R:ℤ)-(r:ℤ)-1)*
    sl2RacahBirth q l m n r ((R:ℤ)-(r:ℤ)))/
    sl2RacahDeath q l m n ((r:ℤ)+1) ((R:ℤ)-(r:ℤ)-1)

def spinRacahGauge (q : ℝ) (l m n R r : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (r-(R-n)),spinRacahGaugeStep q l m n R (R-n+k)

theorem spinRacahGauge_first (q : ℝ) (l m n R : ℕ) :
    spinRacahGauge q l m n R (R-n)=1 := by
  simp only [spinRacahGauge,Nat.sub_self,Finset.range_zero,Finset.prod_empty]

theorem spinRacahGauge_succ (q : ℝ) (l m n R r : ℕ) (hr : R-n≤r) :
    spinRacahGauge q l m n R (r+1)=spinRacahGauge q l m n R r*spinRacahGaugeStep q l m n R r := by
  unfold spinRacahGauge
  have he : r+1-(R-n)=r-(R-n)+1 := by omega
  have hi : R-n+(r-(R-n))=r := by omega
  rw [he,Finset.prod_range_succ,hi]

theorem spinRacahGauge_neighbor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hv : v.val.1.val+1=p.val.1.val) :
    spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val=
      spinRacahGauge q l m n (leftHighestDefect l m n H) v.val.1.val*
        (quantumRacahJacobi q hq hq1 l m n H p v/
          sl2RacahDeath q l m n p.val.1.val p.val.2.val) := by
  have hmin := fixedLeftHighest_minimum_bound l m n H v
  have hd := fixedLeftHighest_defect l m n H p
  have hdv := fixedLeftHighest_defect l m n H v
  have hp₁ : (v.val.1.val:ℤ)+1=(p.val.1.val:ℤ) := by omega
  have hp₂ : (leftHighestDefect l m n H:ℤ)-(v.val.1.val:ℤ)-1=(p.val.2.val:ℤ) := by omega
  have hv₂ : (leftHighestDefect l m n H:ℤ)-(v.val.1.val:ℤ)=(v.val.2.val:ℤ) := by omega
  have hw := spinRacahGauge_succ q l m n (leftHighestDefect l m n H) v.val.1.val hmin
  rw [hv] at hw
  rw [hw]
  congr 1
  unfold spinRacahGaugeStep
  rw [hp₁,hp₂,hv₂,← quantumRacahJacobi_step_sqrt_rates q hq hq1 l m n H p v hv]

theorem spinRacahGauge_death (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hv : v.val.1.val+1=p.val.1.val) :
    sl2RacahDeath q l m n p.val.1.val p.val.2.val*
      spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val=
    quantumRacahJacobi q hq hq1 l m n H p v*
      spinRacahGauge q l m n (leftHighestDefect l m n H) v.val.1.val := by
  have hA := ne_of_gt (quantumRacahJacobi_step_pos q hq hq1 l m n H p v hv)
  have hsq := quantumRacahJacobi_step_sq_rates q hq hq1 l m n H p v hv
  have hD : sl2RacahDeath q l m n p.val.1.val p.val.2.val≠0 := by
    intro hz
    rw [hz,zero_mul] at hsq
    exact hA (sq_eq_zero_iff.mp hsq)
  rw [spinRacahGauge_neighbor q hq hq1 l m n H p v hv]
  field_simp [hD]

theorem spinRacahGauge_birth (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hv : v.val.1.val+1=p.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p v*
      spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val=
    sl2RacahBirth q l m n v.val.1.val v.val.2.val*
      spinRacahGauge q l m n (leftHighestDefect l m n H) v.val.1.val := by
  have hA := ne_of_gt (quantumRacahJacobi_step_pos q hq hq1 l m n H p v hv)
  have hsq := quantumRacahJacobi_step_sq_rates q hq hq1 l m n H p v hv
  have hD : sl2RacahDeath q l m n p.val.1.val p.val.2.val≠0 := by
    intro hz
    rw [hz,zero_mul] at hsq
    exact hA (sq_eq_zero_iff.mp hsq)
  rw [spinRacahGauge_neighbor q hq hq1 l m n H p v hv]
  apply (mul_right_cancel₀ hD)
  calc
    _ = (quantumRacahJacobi q hq hq1 l m n H p v)^2*
          spinRacahGauge q l m n (leftHighestDefect l m n H) v.val.1.val := by field_simp [hD]
    _ = _ := by rw [hsq];ring

end AMSPhysical

#print axioms AMSPhysical.spinRacahGauge_birth
#print axioms AMSPhysical.spinRacahGauge_death

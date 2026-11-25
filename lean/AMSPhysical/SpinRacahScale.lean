import SpinRacahDifference
import QuantumRacahRates
import QuantumChannelNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem square_zpow_even (q : ℝ) (a : ℤ) : (q^2)^a=q^(2*a) := by
  rw [← zpow_natCast q 2,← zpow_mul]
  norm_num

theorem spinRacahForward_scale (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n R r s : ℕ) (hR : r+s=R) :
    q^((m:ℤ)+(n:ℤ)+1)*spinRacahForward (q^2) l m n R r=
      sl2RacahBirth q l m n r s := by
  unfold spinRacahForward spinRacahA spinRacahFourth
  simp only [square_zpow_even]
  have h₁ : -(R:ℤ)-1=-(r:ℤ)-(s:ℤ)-1 := by omega
  have h₂ : (R:ℤ)-(l:ℤ)-(m:ℤ)-1=(r:ℤ)+(s:ℤ)-(l:ℤ)-(m:ℤ)-1 := by omega
  rw [h₁,h₂]
  exact qRacahB_sl2_parameters q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n r s

theorem spinRacahBackward_scale (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n R r s : ℕ) (hR : r+s=R) :
    q^((m:ℤ)+(n:ℤ)+1)*spinRacahBackward (q^2) l m n R r=
      sl2RacahDeath q l m n r s := by
  unfold spinRacahBackward spinRacahA spinRacahFourth
  simp only [square_zpow_even]
  have h₁ : -(R:ℤ)-1=-(r:ℤ)-(s:ℤ)-1 := by omega
  have h₂ : (R:ℤ)-(l:ℤ)-(m:ℤ)-1=(r:ℤ)+(s:ℤ)-(l:ℤ)-(m:ℤ)-1 := by omega
  rw [h₁,h₂]
  exact qRacahD_sl2_parameters q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n r s

theorem spinRacahSpectral_scale (q : ℝ) (hq : 0<q) (m n u : ℕ) :
    q^((m:ℤ)+(n:ℤ)+1)*spinRacahSpectral (q^2) m n u=
      quantumCasimirEigen q ((m:ℤ)+(n:ℤ)-2*(u:ℤ))-quantumCasimirEigen q ((m:ℤ)+(n:ℤ)) := by
  have hq0 := ne_of_gt hq
  unfold spinRacahSpectral spinRacahA qRacahLambda quantumCasimirEigen
  rw [← zpow_natCast (q^2) u]
  simp only [square_zpow_even]
  have hAB : q^(2*(-(m:ℤ)-1))*q^(2*(-(n:ℤ)-1))*q^2=q^(-2*((m:ℤ)+(n:ℤ)+1)) := by
    rw [← zpow_natCast q 2,← zpow_add₀ hq0,← zpow_add₀ hq0]
    congr 1
    ring
  rw [hAB]
  have h₁ : q^((m:ℤ)+(n:ℤ)-2*(u:ℤ)+1)=q^((m:ℤ)+(n:ℤ)+1)/q^(2*(u:ℤ)) := by
    rw [← zpow_sub₀ hq0]
    congr 1
    ring
  have h₂ : q^(-((m:ℤ)+(n:ℤ)-2*(u:ℤ)+1))=q^(2*(u:ℤ))/q^((m:ℤ)+(n:ℤ)+1) := by
    rw [← zpow_sub₀ hq0]
    congr 1
    ring
  have h₃ : q^(-2*((m:ℤ)+(n:ℤ)+1))=(q^((m:ℤ)+(n:ℤ)+1))⁻¹^2 := by
    rw [← zpow_neg,← zpow_natCast (q^(-((m:ℤ)+(n:ℤ)+1))) 2,← zpow_mul]
    congr 1
    ring
  rw [h₁,h₂,h₃,zpow_neg]
  field_simp [zpow_ne_zero ((m:ℤ)+(n:ℤ)+1) hq0,zpow_ne_zero (2*(u:ℤ)) hq0]
  <;> ring

theorem quantum_square_base_ne_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) : q^2≠1 := by
  intro h
  have : q=1 ∨ q= -1 := (sq_eq_one_iff).mp h
  rcases this with h | h
  · exact hq1 h
  · linarith

theorem spinRacahFunction_physical_difference (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n R u r s : ℕ) (h : SpinRacahAdmissible l m n R u)
    (hl : r≤l) (hm : r≤m) (hs : s≤coupledLabel l m r) (hR : r+s=R) :
    sl2RacahBirth q l m n r s*(spinRacahFunction (q^2) l m n R u ((r:ℤ)+1)-spinRacahFunction (q^2) l m n R u r)+
      sl2RacahDeath q l m n r s*(spinRacahFunction (q^2) l m n R u ((r:ℤ)-1)-spinRacahFunction (q^2) l m n R u r)=
      (quantumCasimirEigen q ((m:ℤ)+(n:ℤ)-2*(u:ℤ))-quantumCasimirEigen q ((m:ℤ)+(n:ℤ)))*
        spinRacahFunction (q^2) l m n R u r := by
  have he := spinRacahFunction_difference (q^2) (sq_pos_of_pos hq) (quantum_square_base_ne_one q hq hq1)
    l m n R u r s h hl hm hs hR
  have hh := congrArg (fun x : ℝ => q^((m:ℤ)+(n:ℤ)+1)*x) he
  simpa only [mul_add,← mul_assoc,spinRacahForward_scale q hq hq1 l m n R r s hR,
    spinRacahBackward_scale q hq hq1 l m n R r s hR,spinRacahSpectral_scale q hq m n u] using hh

end AMSPhysical

#print axioms AMSPhysical.spinRacahFunction_physical_difference

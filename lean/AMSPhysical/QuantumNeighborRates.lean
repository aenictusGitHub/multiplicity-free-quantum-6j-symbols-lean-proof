import QuantumJacobiEightFactors
import QuantumRacahRates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def sl2RateNeighborSquare (q : ℝ) (l m n r s : ℤ) : ℝ :=
  (q-q⁻¹)^4*qInteger q r*qInteger q (n-s)*qInteger q (l-r+1)*qInteger q (m-r+1)*
    qInteger q (l+m-r+2)*qInteger q (s+1)*qInteger q (l+m-2*r-s+1)*
    qInteger q (l+m-2*r+n-s+2)/
      (qInteger q (l+m-2*r+1)*(qInteger q (l+m-2*r+2))^2*qInteger q (l+m-2*r+3))

theorem sl2RacahDeath_birth_previous (q : ℝ) (l m n r s : ℤ) :
    sl2RacahDeath q l m n r s*sl2RacahBirth q l m n (r-1) (s+1)=sl2RateNeighborSquare q l m n r s := by
  unfold sl2RacahDeath sl2RacahBirth sl2RateNeighborSquare
  have h₁ : m-(r-1)=m-r+1 := by ring
  have h₂ : l+m-2*(r-1)+n-(s+1)+1=l+m-2*r+n-s+2 := by ring
  have h₃ : l+m-(r-1)+1=l+m-r+2 := by ring
  have h₄ : l+m-2*(r-1)=l+m-2*r+2 := by ring
  have h₅ : l+m-2*(r-1)+1=l+m-2*r+3 := by ring
  rw [h₁,h₂,h₃,h₅,h₄]
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow]
  ring

theorem casimirJacobiNeighborSquare_integer (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    casimirJacobiNeighborSquare q l m n p=sl2RateNeighborSquare q l m n p.1.val p.2.val := by
  have hl := channel_left_bound l m p.1
  have hm := channel_right_bound l m p.1
  have hi := channel_left_bound (coupledLabel l m p.1) n p.2
  have hn := channel_right_bound (coupledLabel l m p.1) n p.2
  have hlm : p.1.val≤l+m := by omega
  have hin : p.2.val≤coupledLabel l m p.1+n := by omega
  unfold casimirJacobiNeighborSquare sl2RateNeighborSquare
  simp only [qnum_eq_qInteger q hq hq1,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Nat.cast_sub hl,Nat.cast_sub hm,Nat.cast_sub hi,Nat.cast_sub hn,Nat.cast_sub hlm,Nat.cast_sub hin,
    coupledLabel_cast l m p.1.val hl hm]

/-- The actual neighboring square is the product of the q-Racah birth and death coefficients. -/
theorem quantumRacahJacobi_step_sq_rates (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    (quantumRacahJacobi q hq hq1 l m n H p v)^2=
      sl2RacahDeath q l m n p.val.1.val p.val.2.val*sl2RacahBirth q l m n v.val.1.val v.val.2.val := by
  rw [quantumRacahJacobi_step_sq q hq hq1 l m n H p v hnext,
    casimirJacobiNeighborSquare_integer q hq hq1]
  have hsecond := fixedLeftHighest_previous_second l m n H p v hnext
  have hr : (v.val.1.val:ℤ)=(p.val.1.val:ℤ)-1 := by omega
  have hs : (v.val.2.val:ℤ)=(p.val.2.val:ℤ)+1 := by omega
  rw [hr,hs,sl2RacahDeath_birth_previous]

theorem quantumRacahJacobi_step_sqrt_rates (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    quantumRacahJacobi q hq hq1 l m n H p v=
      Real.sqrt (sl2RacahDeath q l m n p.val.1.val p.val.2.val*sl2RacahBirth q l m n v.val.1.val v.val.2.val) := by
  rw [← quantumRacahJacobi_step_sq_rates q hq hq1 l m n H p v hnext,Real.sqrt_sq_eq_abs,
    abs_of_pos (quantumRacahJacobi_step_pos q hq hq1 l m n H p v hnext)]

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_step_sq_rates
#print axioms AMSPhysical.quantumRacahJacobi_step_sqrt_rates

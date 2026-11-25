import SpinSearsIdentity
import SearsFactorialSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem square_zpow_nat_power (q : ℝ) (a : ℤ) (k : ℕ) :
    ((q^2)^a)^k=q^(2*a*(k:ℤ)) := by
  rw [← zpow_natCast ((q^2)^a) k,← zpow_mul,square_zpow_even]
  congr 1
  ring

theorem spinSearsClearedTerm_natural (q : ℝ) (hq : 0<q)
    (l m n R u r s k : ℕ) (h : SpinRacahAdmissible l m n R u)
    (hr : r≤m) (hs : s≤n) (hR : r+s=R) :
    searsClearedTerm (q^2) ((q^2)^(-(r:ℤ)))
      ((q^2)^((u:ℤ)-(m:ℤ)-(n:ℤ)-1)) ((q^2)^((r:ℤ)-(l:ℤ)-(m:ℤ)-1))
      ((q^2)^((R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1)) ((q^2)^(-(m:ℤ))) ((q^2)^(-(R:ℤ)))
      ((q^2)^((u:ℤ)+(r:ℤ)-(m:ℤ)-(R:ℤ)-1)) u k=
    naturalSearsTerm q u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1) k := by
  have hQ : q^2≠0 := pow_ne_zero 2 (ne_of_gt hq)
  have hroot := h.rootFirst
  have hsum := h.rootSecond
  have hdB : ((q^2)^((R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1))/
      ((q^2)^((u:ℤ)-(m:ℤ)-(n:ℤ)-1))=(q^2)^(-((l+u-R:ℕ):ℤ)) := by
    rw [← zpow_sub₀ hQ]
    congr 1
    omega
  have hdC : ((q^2)^((R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1))/
      ((q^2)^((r:ℤ)-(l:ℤ)-(m:ℤ)-1))=(q^2)^(-((n-s:ℕ):ℤ)) := by
    rw [← zpow_sub₀ hQ]
    congr 1
    omega
  have heA : ((q^2)^(-(m:ℤ)))/((q^2)^(-(r:ℤ)))=(q^2)^(-((m-r:ℕ):ℤ)) := by
    rw [← zpow_sub₀ hQ]
    congr 1
    omega
  have hfA : ((q^2)^(-(R:ℤ)))/((q^2)^(-(r:ℤ)))=(q^2)^(-(s:ℤ)) := by
    rw [← zpow_sub₀ hQ]
    congr 1
    omega
  have hT : (R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1=-((l+m+n-R+1:ℕ):ℤ) := by omega
  have hx : (u:ℤ)+(r:ℤ)-(m:ℤ)-(R:ℤ)-1=(u:ℤ)-(r:ℤ)-((m-r:ℕ):ℤ)-(s:ℤ)-1 := by omega
  unfold searsClearedTerm naturalSearsTerm
  rw [hdB,hdC,heA,hfA,hT,hx,square_zpow_nat_power,square_zpow_nat_power]
  have hlast : (q^2)^(k*(u-k+1))=q^(2*(k:ℤ)*((u-k+1:ℕ):ℤ)) := by
    rw [← zpow_natCast (q^2) (k*(u-k+1)),square_zpow_even]
    congr 1
    push_cast
    ring
  rw [hlast]
  simp only [square_zpow_even,mul_neg,neg_mul]

/-- The physical-parameter series equals a sum with precisely the Racah
factorial support, before cancellation of its common scalar phase. -/
theorem spinRacah_natural_sears (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n R u r s : ℕ) (h : SpinRacahAdmissible l m n R u)
    (hr : r≤m) (hs : s≤n) (hR : r+s=R) :
    spinRacahFunction (q^2) l m n R u r*
      qPochhammer (q^2) (q^(-2*(m:ℤ))) u*qPochhammer (q^2) (q^(-2*(R:ℤ))) u=
      ∑ k∈Finset.range (u+1),naturalSearsTerm q u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1) k := by
  have he := spinRacah_sears_cleared (q^2) (sq_pos_of_pos hq) (quantum_square_base_ne_one q hq hq1)
    l m n R u r h
  simp_rw [spinSearsClearedTerm_natural q hq l m n R u r s _ h hr hs hR] at he
  simpa only [square_zpow_even,mul_neg,neg_mul] using he

end AMSPhysical

#print axioms AMSPhysical.spinRacah_natural_sears

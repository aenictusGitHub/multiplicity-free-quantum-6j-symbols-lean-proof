import QuantumJacobiNormSquares
import QuantumChannelNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem quantumHighestNorm_outer_neighbor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r k : Fin (min l m+1)) (hkr : k.val+1=r.val) :
    quantumHighestNorm q l m r*(qnum q (l-r.val+1)*qnum q (m-r.val+1)*qnum q (l+m-r.val+2))=
      q^(4*(r.val:ℤ)-2*(m:ℤ)-2)*qnum q r.val*qnum q (coupledLabel l m r+2)*qnum q (coupledLabel l m r+3)*
        quantumHighestNorm q l m k := by
  have h := couplingNormClosed_outer_neighbor q hq l m r.val k.val
    (channel_left_bound l m r) (channel_right_bound l m r) hkr
  rw [← quantumHighestNorm_closed q hq hq1 l m r,← quantumHighestNorm_closed q hq hq1 l m k] at h
  exact h

theorem quantumHighestNorm_root_neighbor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p v : FixedLeftHighest l m n H) (hnext : v.val.1.val+1=p.val.1.val) :
    quantumHighestNorm q (coupledLabel l m v.val.1) n v.val.2*
      (qnum q (n-p.val.2.val)*qnum q (coupledLabel l m p.val.1+1)*qnum q (coupledLabel l m p.val.1+2))=
      q^(4*(p.val.2.val:ℤ)+2-2*(n:ℤ))*qnum q (p.val.2.val+1)*
        qnum q (coupledLabel l m p.val.1-p.val.2.val+1)*qnum q (coupledLabel l m p.val.1+n-p.val.2.val+2)*
          quantumHighestNorm q (coupledLabel l m p.val.1) n p.val.2 := by
  have hsecond := fixedLeftHighest_previous_second l m n H p v hnext
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hlabel : coupledLabel l m v.val.1=coupledLabel l m p.val.1+2 := by unfold coupledLabel;omega
  have hi := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hn := channel_right_bound (coupledLabel l m v.val.1) n v.val.2
  have h := couplingNormClosed_root_neighbor q hq (coupledLabel l m p.val.1) n p.val.2.val hi (by omega)
  have hprev : quantumHighestNorm q (coupledLabel l m v.val.1) n v.val.2=
      couplingNormClosed q (coupledLabel l m p.val.1+2-(p.val.2.val+1)) (n-(p.val.2.val+1)) (p.val.2.val+1) := by
    rw [quantumHighestNorm_closed q hq hq1]
    congr 1 <;> omega
  rw [← hprev,← quantumHighestNorm_closed q hq hq1 (coupledLabel l m p.val.1) n p.val.2] at h
  exact h

theorem casimirLowerStep_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (m n r s : ℕ) (hs : s≤n) :
    casimirLowerStep q m n r s=(q-q⁻¹)^2*q^((n:ℤ)-(m:ℤ)+2*(r:ℤ)-2*(s:ℤ)-2)*qnum q r*qnum q (n-s) := by
  unfold casimirLowerStep
  have hns : (n:ℤ)-(s:ℤ)=((n-s:ℕ):ℤ) := by omega
  rw [hns,← qnum_eq_qInteger q hq hq1,← qnum_eq_qInteger q hq hq1]
  have hp : q^(-(m:ℤ)+2*((r:ℤ)-1))*q^((n:ℤ)-2*(s:ℤ))=
      q^((n:ℤ)-(m:ℤ)+2*(r:ℤ)-2*(s:ℤ)-2) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  linear_combination (q-q⁻¹)^2*qnum q r*qnum q (n-s)*hp

theorem casimirLowerStep_phase_square (q : ℝ) (hq : 0<q) (hq1 : q≠1) (m n r s : ℕ) (hs : s≤n) :
    (casimirLowerStep q m n r s)^2*q^(4*(s:ℤ)+2-2*(n:ℤ))=
      (q-q⁻¹)^4*(qnum q r)^2*(qnum q (n-s))^2*q^(4*(r:ℤ)-2*(m:ℤ)-2) := by
  rw [casimirLowerStep_closed q hq hq1 m n r s hs]
  have hp : (q^((n:ℤ)-(m:ℤ)+2*(r:ℤ)-2*(s:ℤ)-2))^2*q^(4*(s:ℤ)+2-2*(n:ℤ))=
      q^(4*(r:ℤ)-2*(m:ℤ)-2) := by
    rw [sq,← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  linear_combination (q-q⁻¹)^4*(qnum q r)^2*(qnum q (n-s))^2*hp

end AMSPhysical

#print axioms AMSPhysical.quantumHighestNorm_root_neighbor
#print axioms AMSPhysical.casimirLowerStep_phase_square

import QuantumCoupledBasis
import JointEigenCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

/-- Each constructed quantum coupling string terminates at exactly the required
highest-weight dimension, using the full actual tensor-product spectrum. -/
theorem coupledString_truncates (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    coupledString q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m r
      (channel_left_bound l m r) (channel_right_bound l m r) (coupledLabel l m r+1)=0 := by
  classical
  let ρ := finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
  let b := quantumCoupledBasis q hq hq1 l m
  let c (p : CoupledIndex l m) := quantumCasimirEigen q ((l:ℤ)+(m:ℤ)-2*(p.1.val:ℤ))
  let w (p : CoupledIndex l m) := q^((l:ℤ)+(m:ℤ)-2*(p.1.val:ℤ)-2*(p.2.val:ℤ))
  let L := coupledLabel l m r
  let v := coupledString q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m r
    (channel_left_bound l m r) (channel_right_bound l m r) (L+1)
  let c₀ := quantumCasimirEigen q ((l:ℤ)+(m:ℤ)-2*(r.val:ℤ))
  let w₀ := q^((l:ℤ)+(m:ℤ)-2*(r.val:ℤ)-2*((L+1:ℕ):ℤ))
  change v=0
  refine joint_eigenvector_zero b (ρ (uqCasimir q)) (ρ (uqGenerator q 2)) c w ?_ ?_ v c₀ w₀ ?_ ?_ ?_
  · intro p
    rw [show b p=realCoupledVector q hq hq1 l m p.1 p.2 from quantumCoupledBasis_apply q hq hq1 l m p]
    exact coupledString_Casimir q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m p.1 (channel_left_bound l m p.1) (channel_right_bound l m p.1) p.2
      (fun j _ => ne_of_gt (qInteger_pos_real q hq hq1 (j+1:ℕ) (by omega)))
  · intro p
    rw [show b p=realCoupledVector q hq hq1 l m p.1 p.2 from quantumCoupledBasis_apply q hq hq1 l m p]
    exact coupledString_weight q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m p.1 (channel_left_bound l m p.1) (channel_right_bound l m p.1) p.2
  · exact coupledString_Casimir q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m r (channel_left_bound l m r) (channel_right_bound l m r) (L+1)
      (fun j _ => ne_of_gt (qInteger_pos_real q hq hq1 (j+1:ℕ) (by omega)))
  · exact coupledString_weight q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m r (channel_left_bound l m r) (channel_right_bound l m r) (L+1)
  · intro p
    by_cases hc : c p=c₀
    · right
      have hpcast := coupledLabel_cast l m p.1 (channel_left_bound l m p.1) (channel_right_bound l m p.1)
      have hrcast := coupledLabel_cast l m r (channel_left_bound l m r) (channel_right_bound l m r)
      have hp0 : (l:ℤ)+(m:ℤ)-2*(p.1.val:ℤ)∈Set.Ici (0:ℤ) := by
        change 0≤(l:ℤ)+(m:ℤ)-2*(p.1.val:ℤ)
        rw [← hpcast]
        exact Int.natCast_nonneg _
      have hr0 : (l:ℤ)+(m:ℤ)-2*(r.val:ℤ)∈Set.Ici (0:ℤ) := by
        change 0≤(l:ℤ)+(m:ℤ)-2*(r.val:ℤ)
        rw [← hrcast]
        exact Int.natCast_nonneg _
      have hlabel := quantumCasimirEigen_injective_real q hq hq1 hp0 hr0 hc
      intro he
      have hw := zpow_right_injective₀ hq hq1 he
      have hk := Nat.le_of_lt_succ p.2.isLt
      dsimp [w,w₀,L] at hw
      omega
    · exact Or.inl hc

end AMSPhysical

#print axioms AMSPhysical.coupledString_truncates

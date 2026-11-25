import QuantumMixedFusionIndex
import QuantumMixedNormClosed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2600000
noncomputable section
namespace AMSPhysical

theorem mixedFusionHighest_norm_closed (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hrl : r≤l) (hrm : r≤m) :
    mixedTensorBilin q n l m (mixedFusionHighest q n l m r hrl hrm) (mixedFusionHighest q n l m r hrl hrm)=
      mixedCouplingNormClosed q n (l-r) (m-r) r := by
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hrl
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le hrm
  subst l
  subst m
  rw [mixedFusionHighest_add]
  simp only [Nat.add_sub_cancel_left]
  exact mixedHighestVector_norm_closed q hq n a b r hn

theorem mixedFusionHighestAt_norm_closed (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedTensorBilin q n l m (mixedFusionHighestAt q n l m r) (mixedFusionHighestAt q n l m r)=
      mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val :=
  mixedFusionHighest_norm_closed q hq n hn l m r.val _ _

theorem mixedCouplingNormClosed_succ (q : ℝ) (hq : 0<q) (n a b r : ℕ) :
    mixedCouplingNormClosed q n a b (r+1)=
      q^(-2*(b:ℤ))*qnum q (r+1)*qnum q (a+n+b+r+1)/
        (qnum q (r+a+1)*qnum q (r+b+1))*mixedCouplingNormClosed q n a b r := by
  unfold mixedCouplingNormClosed
  have ha : r+1+a=r+a+1 := by omega
  have hb : r+1+b=r+b+1 := by omega
  have hc : a+n+b+(r+1)=a+n+b+r+1 := by omega
  rw [ha,hb,hc]
  rw [qfactorial_succ,qfactorial_succ,qfactorial_succ,qfactorial_succ]
  have he : -2*(b:ℤ)*((r+1:ℕ):ℤ)=(-2*(b:ℤ))+(-2*(b:ℤ)*(r:ℤ)) := by push_cast;ring
  rw [he,zpow_add₀ (ne_of_gt hq)]
  field_simp [qfactorial_ne_zero q hq (r+a),qfactorial_ne_zero q hq (r+b),qfactorial_ne_zero q hq (a+n+b),
    ne_of_gt (qnum_pos q hq (by omega : 0<r+a+1)),ne_of_gt (qnum_pos q hq (by omega : 0<r+b+1))]

end AMSPhysical

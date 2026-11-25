import QuantumMixedFusionNorm
import QuantumMixedNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2600000
noncomputable section
namespace AMSPhysical

/-- Closed physical creation-contraction eigenvalue, with the rank-dependent
factor [l+m+n-r+1] visible rather than hidden in a norm ratio. -/
def mixedCreationSpectralScalar (q : ℝ) (n l m r : ℕ) : ℝ :=
  q^(-2*(l:ℤ)-2*(m:ℤ))*qnum q (r+1)*qnum q (l+m+n-r+1)/
    (qnum q (l+1)*qnum q (m+1))

theorem mixedCreationSpectralScalar_norm_ratio (q : ℝ) (hq : 0<q) (n l m r : ℕ)
    (hrl : r≤l) (hrm : r≤m) :
    q^(-(l:ℤ)-(r:ℤ))*(q^(-(l:ℤ)-(r:ℤ))*mixedCouplingNormClosed q n (l-r) (m-r) (r+1)/
      mixedCouplingNormClosed q n (l-r) (m-r) r)=mixedCreationSpectralScalar q n l m r := by
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hrl
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le hrm
  subst l
  subst m
  simp only [Nat.add_sub_cancel_left]
  rw [mixedCouplingNormClosed_succ q hq]
  have hc : r+a+(r+b)+n-r+1=a+n+b+r+1 := by omega
  unfold mixedCreationSpectralScalar
  rw [hc]
  have hp : q^(-((r+a:ℕ):ℤ)-(r:ℤ))*q^(-((r+a:ℕ):ℤ)-(r:ℤ))*q^(-2*(b:ℤ))=
      q^(-2*((r+a:ℕ):ℤ)-2*((r+b:ℕ):ℤ)) := by
    rw [← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  have hN := ne_of_gt (mixedCouplingNormClosed_pos q hq n a b r)
  field_simp [hN,ne_of_gt (qnum_pos q hq (r+a+1) (by omega)),
    ne_of_gt (qnum_pos q hq (r+b+1) (by omega))]
  linear_combination (qnum q (r+1)*qnum q (a+n+b+r+1))*hp

theorem mixedCreationSpectralScalar_pos (q : ℝ) (hq : 0<q) (n l m r : ℕ) :
    0<mixedCreationSpectralScalar q n l m r := by
  unfold mixedCreationSpectralScalar
  exact div_pos (mul_pos (mul_pos (zpow_pos hq _) (qnum_pos q hq _ (by omega)))
    (qnum_pos q hq _ (by omega))) (mul_pos (qnum_pos q hq _ (by omega)) (qnum_pos q hq _ (by omega)))

end AMSPhysical

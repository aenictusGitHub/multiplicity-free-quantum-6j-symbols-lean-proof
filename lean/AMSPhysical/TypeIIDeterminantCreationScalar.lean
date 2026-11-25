import TypeIIDeterminantMetricScale
import QuantumCreationSpectralScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

theorem typeIIDeterminantMetricScale_creation_step (q:ℝ) (hq:0<q) (h a b d:ℕ):
    typeIIDeterminantMetricScale q h a (b+1) d*qnum q (b+h+1)=
      q^(-2*(h:ℤ))*qnum q (b+1)*typeIIDeterminantMetricScale q h a b d := by
  unfold typeIIDeterminantMetricScale
  rw [show b+1+h=b+h+1 from by omega,qfactorial_succ q (b+h),qfactorial_succ q b]
  have hp:q^(-2*(h:ℤ)*((b+1:ℕ):ℤ))=q^(-2*(h:ℤ))*q^(-2*(h:ℤ)*(b:ℤ)):=by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  rw [hp]
  have hf(k:ℕ):qfactorial q k≠0:=qfactorial_ne_zero q hq k
  field_simp [hf,ne_of_gt (qnum_pos q hq (b+h+1) (by omega))]

/-- The normalized determinant transport has exactly the scalar needed to
match the ACTUAL mixed creation-contraction eigenvalues at shifted labels. -/
theorem mixedCreationSpectralScalar_typeII_shift (q:ℝ) (hq:0<q) (h b c k:ℕ):
    (q^(2*(h:ℤ))*qnum q (b+h+1)/qnum q (b+1))*
      mixedCreationSpectralScalar q 1 (b+h) c k=
      mixedCreationSpectralScalar q (h+1) b c k := by
  unfold mixedCreationSpectralScalar
  rw [show b+h+c+1-k+1=b+c+(h+1)-k+1 from by omega]
  have hp:q^(2*(h:ℤ))*q^(-2*((b+h:ℕ):ℤ)-2*(c:ℤ))=q^(-2*(b:ℤ)-2*(c:ℤ)):=by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  have hb:qnum q (b+1)≠0:=ne_of_gt (qnum_pos q hq (b+1) (by omega))
  have hbh:qnum q (b+h+1)≠0:=ne_of_gt (qnum_pos q hq (b+h+1) (by omega))
  have hc:qnum q (c+1)≠0:=ne_of_gt (qnum_pos q hq (c+1) (by omega))
  field_simp [hb,hbh,hc]
  linear_combination (qnum q (k+1)*qnum q (b+c+(h+1)-k+1))*hp

end AMSPhysical
#print axioms AMSPhysical.mixedCreationSpectralScalar_typeII_shift

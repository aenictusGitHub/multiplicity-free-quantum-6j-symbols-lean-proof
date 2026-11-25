import TypeIIDeterminantCreationScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def typeIICreationIsometryScalar (q:ℝ) (h a b d:ℕ):ℝ:=
  Real.sqrt (typeIIDeterminantMetricScale q h a b d)/
    Real.sqrt (typeIIDeterminantMetricScale q h a (b+1) d)

theorem typeIICreationIsometryScalar_pos (q:ℝ) (hq:0<q) (h a b d:ℕ):
    0<typeIICreationIsometryScalar q h a b d:=
  div_pos (Real.sqrt_pos.mpr (typeIIDeterminantMetricScale_pos q hq h a b d))
    (Real.sqrt_pos.mpr (typeIIDeterminantMetricScale_pos q hq h a (b+1) d))

theorem typeIICreationIsometryScalar_sq (q:ℝ) (hq:0<q) (h a b d:ℕ):
    (typeIICreationIsometryScalar q h a b d)^2=
      q^(2*(h:ℤ))*qnum q (b+h+1)/qnum q (b+1) := by
  unfold typeIICreationIsometryScalar
  rw [div_pow,Real.sq_sqrt (typeIIDeterminantMetricScale_pos q hq h a b d).le,
    Real.sq_sqrt (typeIIDeterminantMetricScale_pos q hq h a (b+1) d).le]
  have he:=typeIIDeterminantMetricScale_creation_step q hq h a b d
  have hp:q^(2*(h:ℤ))*q^(-2*(h:ℤ))=1:=by
    rw [← zpow_add₀ (ne_of_gt hq)]
    rw [show 2*(h:ℤ)+ -2*(h:ℤ)=0 from by ring,zpow_zero]
  have hb:qnum q (b+1)≠0:=ne_of_gt (qnum_pos q hq (b+1) (by omega))
  have hC:typeIIDeterminantMetricScale q h a (b+1) d≠0:=
    ne_of_gt (typeIIDeterminantMetricScale_pos q hq h a (b+1) d)
  field_simp [hb,hC]
  calc
    _=(q^(2*(h:ℤ))*q^(-2*(h:ℤ)))*qnum q (b+1)*typeIIDeterminantMetricScale q h a b d:=by
      rw [hp]
      ring
    _=q^(2*(h:ℤ))*(typeIIDeterminantMetricScale q h a (b+1) d*qnum q (b+h+1)):=by
      rw [he]
      ring
    _=_:=by ring

theorem typeIICreationIsometryScalar_spectral (q:ℝ) (hq:0<q) (h a b c d k:ℕ):
    (typeIICreationIsometryScalar q h a b d)^2*
      mixedCreationSpectralScalar q 1 (b+h) c k=
      mixedCreationSpectralScalar q (h+1) b c k := by
  rw [typeIICreationIsometryScalar_sq q hq,mixedCreationSpectralScalar_typeII_shift q hq]

end AMSPhysical
#print axioms AMSPhysical.typeIICreationIsometryScalar_spectral

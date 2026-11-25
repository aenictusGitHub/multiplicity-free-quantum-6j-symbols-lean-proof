import BilinearAdjoint
import QuantumCasimir

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The actual compact real form, expressed by adjoints of the independently presented generators. -/
structure IsCompactQuantumPair (q : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) : Prop where
  adjE : PairAdjoint B (ρ (uqGenerator q 0)) (ρ (uqGenerator q 2)*ρ (uqGenerator q 1))
  adjF : PairAdjoint B (ρ (uqGenerator q 1)) (ρ (uqGenerator q 0)*ρ (uqGenerator q 3))
  adjK : PairAdjoint B (ρ (uqGenerator q 2)) (ρ (uqGenerator q 2))
  adjKi : PairAdjoint B (ρ (uqGenerator q 3)) (ρ (uqGenerator q 3))

theorem uq_FE_conjugation (q : ℝ) (hq : q≠0) :
    (uqGenerator q 2*uqGenerator q 1)*(uqGenerator q 0*uqGenerator q 3)=
      uqGenerator q 1*uqGenerator q 0 := by
  have hp : q^(-2:ℤ)*q^2=1 := by
    rw [← zpow_natCast q 2,← zpow_add₀ hq]
    norm_num
  calc
    (uqGenerator q 2*uqGenerator q 1)*(uqGenerator q 0*uqGenerator q 3)=
        (uqGenerator q 2*uqGenerator q 1)*uqGenerator q 0*uqGenerator q 3 := by noncomm_ring
    _=q^(-2:ℤ) • ((uqGenerator q 1*uqGenerator q 2)*uqGenerator q 0*uqGenerator q 3) := by
      rw [uq_weightF,smul_mul_assoc,smul_mul_assoc]
    _=q^(-2:ℤ) • (uqGenerator q 1*(uqGenerator q 2*uqGenerator q 0)*uqGenerator q 3) := by
      rw [mul_assoc (uqGenerator q 1) (uqGenerator q 2) (uqGenerator q 0)]
    _=(q^(-2:ℤ)*q^2) • (uqGenerator q 1*(uqGenerator q 0*uqGenerator q 2)*uqGenerator q 3) := by
      rw [uq_weightE,mul_smul_comm,smul_mul_assoc,smul_smul]
    _=uqGenerator q 1*uqGenerator q 0 := by
      rw [hp,one_smul,mul_assoc, mul_assoc,uq_inverse,mul_one]

theorem IsCompactQuantumPair.casimir {q : ℝ} (hq : q≠0)
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V}
    (h : IsCompactQuantumPair q B ρ) : PairAdjoint B (ρ (uqCasimir q)) (ρ (uqCasimir q)) := by
  have hFE := h.adjF.mul h.adjE
  have hconj : (ρ (uqGenerator q 2)*ρ (uqGenerator q 1))*(ρ (uqGenerator q 0)*ρ (uqGenerator q 3))=
      ρ (uqGenerator q 1)*ρ (uqGenerator q 0) := by
    simpa only [map_mul] using congrArg ρ (uq_FE_conjugation q hq)
  rw [hconj] at hFE
  simpa only [uqCasimir,map_add,map_smul,map_mul] using
    ((hFE.smul ((q-q⁻¹)^2)).add (h.adjK.smul q)).add (h.adjKi.smul q⁻¹)

end AMSPhysical

#print axioms AMSPhysical.IsCompactQuantumPair.casimir

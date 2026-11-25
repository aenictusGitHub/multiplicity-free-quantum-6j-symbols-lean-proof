import CompactTypeAPair
import QuantumTypeAVectorInvariant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem compact_weight_zero_highest_F (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hCompact : IsCompactTypeAPair q n B ρ) (hDef : ∀ x,B x x=0 → x=0)
    (v : V) (hE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=v) (i : Fin n) :
    ρ (typeAAlgebraGenerator q n i 1) v=0 := by
  have hKi : ρ (typeAAlgebraGenerator q n i 3) v=v := by
    have hinv : ρ (typeAAlgebraGenerator q n i 3)*ρ (typeAAlgebraGenerator q n i 2)=1 := by
      rw [← map_mul,uqA_inverse',map_one]
    have h := DFunLike.congr_fun hinv v
    simpa only [Module.End.mul_apply,hK,Module.End.one_apply] using h
  have hEF : ρ (typeAAlgebraGenerator q n i 0) (ρ (typeAAlgebraGenerator q n i 1) v)=0 := by
    have hc : ρ (typeAAlgebraGenerator q n i 0)*ρ (typeAAlgebraGenerator q n i 1)-
        ρ (typeAAlgebraGenerator q n i 1)*ρ (typeAAlgebraGenerator q n i 0)=
        (q-q⁻¹)⁻¹ • (ρ (typeAAlgebraGenerator q n i 2)-ρ (typeAAlgebraGenerator q n i 3)) := by
      rw [← map_mul,← map_mul,← map_sub,uqA_commutator,map_smul,map_sub]
    have h := DFunLike.congr_fun hc v
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,hE,map_zero,hK,hKi,
      sub_self,smul_zero,sub_zero] at h
    exact h
  have hKiF : ρ (typeAAlgebraGenerator q n i 3) (ρ (typeAAlgebraGenerator q n i 1) v)=
      q^(typeACartan n i i) • ρ (typeAAlgebraGenerator q n i 1) v := by
    rw [← Module.End.mul_apply,← map_mul,uqA_Kinv_F q hq n i i,map_smul,map_mul,
      LinearMap.smul_apply,Module.End.mul_apply,hKi]
  apply hDef
  rw [hCompact.adjF i]
  change B v (ρ (typeAAlgebraGenerator q n i 0)
    (ρ (typeAAlgebraGenerator q n i 3) (ρ (typeAAlgebraGenerator q n i 1) v)))=0
  rw [hKiF,map_smul,hEF,smul_zero,map_zero]

/-- A weight-zero highest vector in an actual compact representation is
invariant under the ENTIRE presented quantum algebra. -/
theorem compact_weight_zero_highest_invariant (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hCompact : IsCompactTypeAPair q n B ρ) (hDef : ∀ x,B x x=0 → x=0)
    (v : V) (hE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=v) :
    ∀ z : UqTypeA q n,ρ z v=typeAQuantumCounit q n z • v := by
  apply typeA_invariantVector_of_generators q n ρ v
  intro i t
  fin_cases t
  · simpa [typeAQuantumCounit_generator] using hE i
  · simpa [typeAQuantumCounit_generator] using compact_weight_zero_highest_F q hq n ρ B hCompact hDef v hE hK i
  · simpa [typeAQuantumCounit_generator] using hK i
  · have hinv : ρ (typeAAlgebraGenerator q n i 3)*ρ (typeAAlgebraGenerator q n i 2)=1 := by
      rw [← map_mul,uqA_inverse',map_one]
    have h := DFunLike.congr_fun hinv v
    simpa [Module.End.mul_apply,hK,typeAQuantumCounit_generator] using h

end AMSPhysical

import QuantumMixedRawChannelSpectrum
import QuantumReverseMixedCreation
import QuantumReverseFusion
import BilinearAdjointTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def reverseMixedRawAnnihilation (q : ℝ) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) →ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  (mixedReflection n l m).toLinearMap.comp
    ((mixedFiniteRawAnnihilation q n l m).comp (mixedReflection n (l+1) (m+1)).symm.toLinearMap)

theorem reverseMixedRawAnnihilation_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    reverseMixedTensorBilin q n (l+1) (m+1) (reverseMixedFiniteCreation q n l m v) w=
      reverseMixedTensorBilin q n l m v (mixedAnnihilationScale q n l m • reverseMixedRawAnnihilation q n l m w) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  have ht:=bilinearAdjoint_transport (V:=V) (W:=W) (V':=V) (W':=W)
    (mixedTensorBilin q n l m) (mixedTensorBilin q n (l+1) (m+1))
    (reverseMixedTensorBilin q n l m) (reverseMixedTensorBilin q n (l+1) (m+1))
    (mixedReflection n l m) (mixedReflection n (l+1) (m+1))
    (mixedReflection_isometry q (ne_of_gt hq) n l m) (mixedReflection_isometry q (ne_of_gt hq) n (l+1) (m+1))
    (mixedFiniteCreation q n l m) (mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m)
    (mixedFiniteRawAnnihilation_adjoint q hq hq1 n l m) v w
  change reverseMixedTensorBilin q n (l+1) (m+1)
    (mixedReflection n (l+1) (m+1) (mixedFiniteCreation q n l m ((mixedReflection n l m).symm v))) w=
    reverseMixedTensorBilin q n l m v
      (mixedReflection n l m (mixedAnnihilationScale q n l m •
        mixedFiniteRawAnnihilation q n l m ((mixedReflection n (l+1) (m+1)).symm w))) at ht
  rw [map_smul] at ht
  exact ht

theorem reverseMixedRawRadial_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex (l+1) (m+1))
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (hv : v∈reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (l+1) (m+1) r) :
    reverseMixedFiniteCreation q n l m (reverseMixedRawAnnihilation q n l m v)=
      quantumCupLeftEigenvalue q n (l+1) (m+1) 0 r.val • v := by
  rw [← reverseMixedFusionChannelAt_map] at hv
  obtain ⟨w,hw,rfl⟩:=hv
  unfold reverseMixedFiniteCreation reverseMixedRawAnnihilation
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  rw [mixedFiniteRawRadial_channel q hq hq1 n hn l m r w hw,map_smul]

end AMSPhysical
#print axioms AMSPhysical.reverseMixedRawRadial_channel

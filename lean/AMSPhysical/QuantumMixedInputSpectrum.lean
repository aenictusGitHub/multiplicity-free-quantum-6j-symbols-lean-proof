import QuantumMixedContractionSpectrum
import QuantumMixedRawChannelSpectrum
import QuantumMixedExactEigenspaces

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The adjoint-creation radial eigenvalue holds on the entire input
irreducible channel, including contraction zero. -/
theorem mixedFiniteContractionCreation_channel (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (l m:ℕ) (r:MixedFusionIndex l m)
    (v:quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hv:v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r):
    mixedFiniteContraction q hq n l m (mixedFiniteCreation q n l m v)=
      mixedCreationSpectralScalar q n l m r.val • v := by
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI:AddCommGroup W:=inferInstance
  letI:Module ℝ W:=inferInstance
  apply commutant_eigen_on_cyclic (V:=W)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    ((mixedFiniteContraction q hq n l m).comp (mixedFiniteCreation q n l m)) _
    (mixedFusionHighestAt q n l m r) (mixedCreationSpectralScalar q n l m r.val)
    (mixedFiniteContractionCreation_highest q hq hq1 n hn l m r) v hv
  intro z w
  change mixedFiniteContraction q hq n l m (mixedFiniteCreation q n l m
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z w))=_
  rw [mixedFiniteCreation_intertwines,mixedFiniteContraction_intertwines q hq hq1]
  rfl

theorem mixedCreationSpectralScalar_injective (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n) (l m:ℕ):
    Function.Injective (fun r:MixedFusionIndex l m=>mixedCreationSpectralScalar q n l m r.val) := by
  intro r s he
  change mixedCreationSpectralScalar q n l m r.val=mixedCreationSpectralScalar q n l m s.val at he
  rw [mixedCreationSpectralScalar_raw q hq hq1 n l m r.val (channel_left_bound l m r),
    mixedCreationSpectralScalar_raw q hq hq1 n l m s.val (channel_left_bound l m s)] at he
  have hh:=mul_left_cancel₀ (ne_of_gt (mixedAnnihilationScale_pos q hq hq1 n l m)) he
  have hi: mixedFusionIndexSucc l m r=mixedFusionIndexSucc l m s:=
    mixedRawRadialEigenvalue_injective q hq hq1 n hn (l+1) (m+1) hh
  apply Fin.ext
  have hv:=congrArg Fin.val hi
  change r.val+1=s.val+1 at hv
  omega

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteContractionCreation_channel
#print axioms AMSPhysical.mixedCreationSpectralScalar_injective

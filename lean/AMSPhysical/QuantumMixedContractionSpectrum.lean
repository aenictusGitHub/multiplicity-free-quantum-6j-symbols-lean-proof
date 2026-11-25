import QuantumMixedContractionHighest
import QuantumCreationSpectralScalar
import QuantumMixedFusionComplete
import CyclicCommutantEigenvalue

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFiniteContractionCreation_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedFiniteContraction q hq n l m
      (mixedFiniteCreation q n l m (mixedFusionHighestAt q n l m r))=
      mixedCreationSpectralScalar q n l m r.val • mixedFusionHighestAt q n l m r := by
  rw [mixedFiniteCreation_highest q hq hq1 n hn,map_smul,mixedFiniteContraction_highest q hq hq1 n hn,smul_smul,
    mixedCreationSpectralScalar_norm_ratio q hq n l m r.val (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)]

theorem mixedFiniteCreationContraction_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedFiniteCreation q n l m
      (mixedFiniteContraction q hq n l m (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r)))=
      mixedCreationSpectralScalar q n l m r.val • mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r) := by
  rw [mixedFiniteContraction_highest q hq hq1 n hn,map_smul,mixedFiniteCreation_highest q hq hq1 n hn,smul_smul,mul_comm,
    mixedCreationSpectralScalar_norm_ratio q hq n l m r.val (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)]

/-- The closed contraction eigenvalue holds on the ENTIRE physical channel,
not just its highest vector. -/
theorem mixedFiniteCreationContraction_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (hv : v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (l+1) (m+1) (mixedFusionIndexSucc l m r)) :
    mixedFiniteCreation q n l m (mixedFiniteContraction q hq n l m v)=
      mixedCreationSpectralScalar q n l m r.val • v := by
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  apply commutant_eigen_on_cyclic (V:=W)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1))
    ((mixedFiniteCreation q n l m).comp (mixedFiniteContraction q hq n l m)) _
    (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r))
    (mixedCreationSpectralScalar q n l m r.val)
    (mixedFiniteCreationContraction_highest q hq hq1 n hn l m r) v hv
  intro z w
  change mixedFiniteCreation q n l m (mixedFiniteContraction q hq n l m
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) z w))=_
  rw [mixedFiniteContraction_intertwines q hq hq1,mixedFiniteCreation_intertwines]
  rfl

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreationContraction_channel

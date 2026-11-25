import QuantumTypeIIRightCreation
import QuantumMixedInputSpectrum
import TensorRightEigenchannel
import QuantumTypeIIRightBasis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalTypeIIRightContraction (q:ℝ) (hq:0<q) (n a b c:ℕ):
    quantumOccupationTripleSpace n a (b+1) (c+1) →ₗ[ℝ] quantumOccupationTripleSpace n a b c:=
  TensorProduct.map LinearMap.id (mixedFiniteContraction q hq n b c)

theorem physicalTypeIIRightCreation_adjoint (q:ℝ) (hq:0<q) (n a b c:ℕ)
    (v:quantumOccupationTripleSpace n a b c) (w:quantumOccupationTripleSpace n a (b+1) (c+1)):
    physicalTypeIITripleBilin q n a (b+1) (c+1) (physicalTypeIIRightCreation q n a b c v) w=
      physicalTypeIITripleBilin q n a b c v (physicalTypeIIRightContraction q hq n a b c w) := by
  induction v using TensorProduct.induction_on with
  | zero=>simp
  | add v v' hv hv'=>simp only [map_add,LinearMap.add_apply,hv,hv']
  | tmul x u=>
    induction w using TensorProduct.induction_on with
    | zero=>simp
    | add w w' hw hw'=>simp only [map_add,hw,hw']
    | tmul y v=>
      simp only [physicalTypeIIRightCreation,physicalTypeIIRightContraction,TensorProduct.map_tmul,
        LinearMap.id_apply,physicalTypeIITripleBilin,tensorWeightedBilin_tmul]
      change occupationCompactBilin q n a x y*
          mixedTensorBilin q n (b+1) (c+1) (mixedFiniteCreation q n b c u) v=
        occupationCompactBilin q n a x y*
          mixedTensorBilin q n b c u (mixedFiniteContraction q hq n b c v)
      rw [mixedFiniteContraction_adjoint]

theorem physicalTypeIIRightCreation_radial_channel (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (a b c:ℕ) (t:QuantumCupIndex a c b) (v:quantumOccupationTripleSpace n a b c)
    (hv:v∈physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t):
    physicalTypeIIRightContraction q hq n a b c (physicalTypeIIRightCreation q n a b c v)=
      mixedCreationSpectralScalar q n b c (typeIIRightIndex a b c t).val • v := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) a
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) b ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  letI:AddCommGroup W:=inferInstance
  letI:Module ℝ W:=inferInstance
  have he:=tensorRight_eigen_on_range (V:=V) (W:=W)
    ((mixedFiniteContraction q hq n b c).comp (mixedFiniteCreation q n b c))
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n b c (typeIIRightIndex a b c t))
    (mixedCreationSpectralScalar q n b c (typeIIRightIndex a b c t).val)
    (mixedFiniteContractionCreation_channel q hq hq1 n hn b c (typeIIRightIndex a b c t)) v hv
  have hc: (physicalTypeIIRightContraction q hq n a b c).comp (physicalTypeIIRightCreation q n a b c)=
      TensorProduct.map (LinearMap.id:Module.End ℝ V)
        ((mixedFiniteContraction q hq n b c).comp (mixedFiniteCreation q n b c)):=by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact (DFunLike.congr_fun hc v).trans he

theorem physicalTypeIIRightCreation_gram_channel (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (a b c:ℕ) (t:QuantumCupIndex a c b) (v w:quantumOccupationTripleSpace n a b c)
    (hw:w∈physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t):
    physicalTypeIITripleBilin q n a (b+1) (c+1)
      (physicalTypeIIRightCreation q n a b c v) (physicalTypeIIRightCreation q n a b c w)=
      mixedCreationSpectralScalar q n b c (typeIIRightIndex a b c t).val*
        physicalTypeIITripleBilin q n a b c v w := by
  rw [physicalTypeIIRightCreation_adjoint q hq,physicalTypeIIRightCreation_radial_channel q hq hq1 n hn a b c t w hw,
    map_smul,smul_eq_mul]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIRightCreation_gram_channel

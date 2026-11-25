import GlobalTypeIIRightBoundary
import GlobalMixedCreationCoherence
import GlobalCupCreationCoherence
import QuantumTypeIIChannelGauge
import QuantumTypeIICreationGram

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFiniteCreation_mem_successor_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (b c : ℕ) (r : MixedFusionIndex b c)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) b ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c)
    (hv : v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n b c r) :
    mixedFiniteCreation q n b c v ∈ mixedFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n (b+1) (c+1) (mixedFusionIndexSucc b c r) := by
  have hx : v∈(mixedFusionHighestRealization q hq hq1 n hn b c r).channel := by
    rwa [mixedFusionHighestRealization_channel]
  have he:=mixedFiniteCreation_channel_transport q hq hq1 n hn b c r ⟨v,hx⟩
  rw [he,← mixedFusionHighestRealization_channel q hq hq1 n hn (b+1) (c+1) (mixedFusionIndexSucc b c r)]
  exact Submodule.smul_mem _ _
    (((mixedFusionHighestRealization q hq hq1 n hn b c r).transport (ne_of_gt hq)
      (mixedCreationTargetRealization q hq hq1 n hn b c r) ⟨v,hx⟩).property)

theorem typeIIRightIndex_creation (a b c : ℕ) (t : QuantumCupIndex a c b) :
    typeIIRightIndex a (b+1) (c+1) (cupCreateRightIndex a c b t) =
      mixedFusionIndexSucc b c (typeIIRightIndex a b c t) := by
  apply Fin.ext
  have ht:=t.val.isLt
  simp only [typeIIRightIndex,mixedFusionSwapIndex,physicalTypeIRightIndex,
    cupCreateRightIndex,mixedFusionIndexSucc]
  omega

theorem physicalTypeIIRightCreation_mem_successor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c : ℕ) (t : QuantumCupIndex a c b)
    (v : quantumOccupationTripleSpace n a b c)
    (hv : v∈physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t) :
    physicalTypeIIRightCreation q n a b c v ∈ physicalTypeIIRightChannel q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n a (b+1) (c+1) (cupCreateRightIndex a c b t) := by
  obtain ⟨u,hu⟩:=hv
  rw [← hu]
  let X:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n b c (typeIIRightIndex a b c t)
  let Y:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (b+1) (c+1)
    (typeIIRightIndex a (b+1) (c+1) (cupCreateRightIndex a c b t))
  let F : X →ₗ[ℝ] Y := ((mixedFiniteCreation q n b c).comp X.subtype).codRestrict Y (by
    intro x
    dsimp only [LinearMap.comp_apply,Submodule.subtype_apply,Y]
    rw [typeIIRightIndex_creation]
    exact mixedFiniteCreation_mem_successor_channel q hq hq1 n hn b c (typeIIRightIndex a b c t) x.val x.property)
  refine ⟨TensorProduct.map LinearMap.id F u,?_⟩
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw]
  | tmul x y => rfl

def typeIIRightCreationScale (q : ℝ) (n a b c : ℕ) (t : QuantumCupIndex a c b) : ℝ :=
  Real.sqrt (mixedCreationSpectralScalar q n b c (typeIIRightIndex a b c t).val)

theorem typeIIRightCreationScale_pos (q : ℝ) (hq : 0<q) (n a b c : ℕ) (t : QuantumCupIndex a c b) :
    0 < typeIIRightCreationScale q n a b c t :=
  Real.sqrt_pos.mpr (mixedCreationSpectralScalar_pos q hq n b c _)

def typeIIRightCreatedUnit (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :=
  (typeIIRightCreationScale q (h+1) a b c t)⁻¹ •
    physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) a b c d (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t)

theorem typeIIRightCreatedUnit_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    (typeIIRightCreatedUnit q hq hq1 h a b c d hbal t).val∈
      physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a (b+1) (c+1) (cupCreateRightIndex a c b t) :=
  Submodule.smul_mem _ _ (physicalTypeIIRightCreation_mem_successor q hq hq1 (h+1) (by omega) a b c t _
    (physicalTypeIICalibratedRight_mem q hq hq1 h a b c d hbal t))

theorem typeIIRightCreatedUnit_norm_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    physicalTypeIITripleBilin q (h+1) a (b+1) (c+1)
      (typeIIRightCreatedUnit q hq hq1 h a b c d hbal t).val
      (typeIIRightCreatedUnit q hq hq1 h a b c d hbal t).val = 1 := by
  unfold typeIIRightCreatedUnit
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul]
  change (typeIIRightCreationScale q (h+1) a b c t)⁻¹ *
    ((typeIIRightCreationScale q (h+1) a b c t)⁻¹ *
      physicalTypeIITripleBilin q (h+1) a (b+1) (c+1)
        (physicalTypeIIRightCreation q (h+1) a b c _)
        (physicalTypeIIRightCreation q (h+1) a b c _))=1
  simp only [Submodule.subtype_apply]
  rw [physicalTypeIIRightCreation_gram_channel q hq hq1 (h+1) (by omega) a b c t _ _
    (physicalTypeIICalibratedRight_mem q hq hq1 h a b c d hbal t),
    physicalTypeIICalibratedRight_unit,mul_one]
  have hp:=mixedCreationSpectralScalar_pos q hq (h+1) b c (typeIIRightIndex a b c t).val
  have hs:=Real.sq_sqrt hp.le
  have hn:=ne_of_gt (typeIIRightCreationScale_pos q hq (h+1) a b c t)
  change (typeIIRightCreationScale q (h+1) a b c t)⁻¹ *
    ((typeIIRightCreationScale q (h+1) a b c t)⁻¹ * _)=1
  change (typeIIRightCreationScale q (h+1) a b c t)^2=_ at hs
  rw [← hs]
  field_simp

theorem typeIIRightCreatedUnit_first_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    0 < typeIIShiftedSelectedCoordinate 0 a (b+1) (c+1) d
      (typeIIZeroCommonIndex a (b+1) (c+1) d)
      (twoVertexTripleProjection (h+1) (by omega) a (b+1) (c+1)
        (typeIIRightCreatedUnit q hq hq1 h a b c d hbal t).val) := by
  rw [← standardBoundaryCoordinate_eq_typeIISelected]
  simp only [typeIIZeroCommonIndex,Fin.val_mk,Nat.add_zero]
  unfold typeIIRightCreatedUnit
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul]
  apply mul_pos (inv_pos.mpr (typeIIRightCreationScale_pos q hq (h+1) a b c t))
  change 0 < standardBoundaryCoordinate a (b+1) (c+1) 0 0
    (twoVertexTripleProjection (h+1) (by omega) a (b+1) (c+1)
      (physicalTypeIIRightCreation q (h+1) a b c
        (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val))
  rw [physicalTypeIIRightCreation_boundary]
  have he:=standardBoundaryCoordinate_creation q a b c 0 0
    (twoVertexTripleProjection (h+1) (by omega) a b c
      (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val)
  simp only [Nat.add_zero,Nat.sub_zero,if_true,mul_zero,sub_zero] at he
  rw [he]
  apply mul_pos (zpow_pos hq _)
  have hp:=physicalTypeIICalibratedRight_first_boundary_pos q hq hq1 h a b c d hbal t
  rw [← standardBoundaryCoordinate_eq_typeIISelected] at hp
  simpa only [typeIIZeroCommonIndex,Fin.val_mk,Nat.add_zero] using hp

/-- Actual calibrated right channels preserve their phase under each
change of mixed-pair realization. The scalar is positive and depends only
on that mixed vertex, not on the attached exterior leg or quadruple. -/
theorem physicalTypeIICalibratedRight_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) a b c d (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t) =
      typeIIRightCreationScale q (h+1) a b c t •
        physicalTypeIICalibratedRight q hq hq1 h a (b+1) (c+1) d (by omega)
          (cupCreateRightIndex a c b t) := by
  have hu : typeIIRightCreatedUnit q hq hq1 h a b c d hbal t =
      physicalTypeIICalibratedRight q hq hq1 h a (b+1) (c+1) d (by omega)
        (cupCreateRightIndex a c b t) :=
    physicalTypeIICalibratedRight_unique_positive q hq hq1 h a (b+1) (c+1) d (by omega)
      (cupCreateRightIndex a c b t) _
      (typeIIRightCreatedUnit_mem q hq hq1 h a b c d hbal t)
      (typeIIRightCreatedUnit_norm_one q hq hq1 h a b c d hbal t)
      (typeIIRightCreatedUnit_first_boundary_pos q hq hq1 h a b c d hbal t)
  have hn:=ne_of_gt (typeIIRightCreationScale_pos q hq (h+1) a b c t)
  calc
    _ = typeIIRightCreationScale q (h+1) a b c t •
      typeIIRightCreatedUnit q hq hq1 h a b c d hbal t := by
        unfold typeIIRightCreatedUnit
        rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
    _ = _ := by rw [hu]

end AMSPhysical
#print axioms AMSPhysical.typeIIRightCreatedUnit_norm_one
#print axioms AMSPhysical.physicalTypeIICalibratedRight_creation

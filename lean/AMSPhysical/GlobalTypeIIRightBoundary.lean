import GlobalRightTreeBoundary
import PhysicalTypeIICalibratedGauge
import TypeIISelectedCoordinateExtension
import QuantumClebschLastFormula
import QuantumTypeIIChannelGauge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeIIZeroCommonIndex (a b c d : ℕ) : TypeIICommonIndex a b c d := ⟨0,by omega⟩

/-- Every shifted standard right channel has a strictly positive selected
zero boundary. This is a one-term CG evaluation, not a fitted AMS entry. -/
theorem typeIIStandardShiftedRight_first_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    0 < typeIIShiftedSelectedCoordinate h a b c d (typeIIZeroCommonIndex a b c d)
      (standardTypeIIBoundaryEquiv (a+h) (b+h) c
        (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t).val) := by
  rw [← standardBoundaryCoordinate_eq_typeIISelected]
  simp only [typeIIZeroCommonIndex,Fin.val_mk,Nat.zero_add]
  let j : Fin (b+h+1) := ⟨h,by omega⟩
  have he:=standardTypeIIBoundaryEquiv_coordinate (a+h) (b+h) c
    (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t).val j 0
  change standardBoundaryCoordinate (a+h) (b+h) c h 0 _ = _ at he
  rw [he]
  change 0 < (((standardWeightBasis (K:=ℝ) (a+h)).tensorProduct (standardWeightBasis (K:=ℝ) (b+h))).tensorProduct
    (standardWeightBasis (K:=ℝ) c)).repr
      (quantumRightTreeHighest q hq hq1 (a+h) (b+h) c
        (typeIIShiftedRightPath h a b c t).1 (typeIIShiftedRightPath h a b c t).2) ((0,j),Fin.last c)
  rw [quantumRightTreeHighest_first_coordinate]
  apply mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))
  let p:=typeIIShiftedRightPath h a b c t
  have ht:=t.val.isLt
  have ha : (rightRootIndexPair (a+h) (b+h) c p 0).2.val=(c-p.1.val)+h := by
    simp only [rightRootIndexPair,couplingBasisIndex,Fin.val_zero,Nat.sub_zero]
    change t.val.val+h=c-(c-t.val.val)+h
    omega
  change 0 < standardClebschCoefficient q hq hq1 (b+h) c p.1
    (rightRootIndexPair (a+h) (b+h) c p 0).2 (h:ℤ) (c:ℤ)
  rw [standardClebschCoefficient_last_closed q hq hq1 (b+h) c p.1
    (rightRootIndexPair (a+h) (b+h) c p 0).2 h ha]
  exact div_pos
    (mul_pos (mul_pos (mul_pos
      (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))
      (zpow_pos hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))

/-- The calibrated physical Type-II right vector itself, in every rank,
has a positive literal highest/highest/opposite-first boundary coefficient. -/
theorem physicalTypeIICalibratedRight_first_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    0 < typeIIShiftedSelectedCoordinate 0 a b c d (typeIIZeroCommonIndex a b c d)
      (twoVertexTripleProjection (h+1) (by omega) a b c
        (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val) := by
  have he:=typeIIShiftedUnitBoundaryMap_coordinate q hq hq1 h a b c d hbal
    (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t) (typeIIZeroCommonIndex a b c d)
  unfold typeIIShiftedUnitBoundaryMap at he
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply,
    physicalTypeIICalibratedRight_standard,typeIIZeroCommonIndex,Fin.val_mk,
    Nat.cast_zero,mul_zero,neg_zero,zpow_zero,mul_one] at he
  have hp:=typeIIStandardShiftedRight_first_boundary_pos q hq hq1 h a b c d hbal t
  dsimp only [typeIIZeroCommonIndex] at hp ⊢
  rw [he] at hp
  have hα : 0 < (Real.sqrt (typeIIDeterminantMetricScale q h a b d))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (typeIIDeterminantMetricScale_pos q hq h a b d))
  nlinarith

/-- A positive literal boundary fixes the entire physical right-channel
phase uniquely, simultaneously for all admissible labels and ranks. -/
theorem physicalTypeIICalibratedRight_unique_positive (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d)
    (hv : v.val∈physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c t)
    (hvn : physicalTypeIITripleBilin q (h+1) a b c v.val v.val=1)
    (hvb : 0 < typeIIShiftedSelectedCoordinate 0 a b c d (typeIIZeroCommonIndex a b c d)
      (twoVertexTripleProjection (h+1) (by omega) a b c v.val)) :
    v=physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t := by
  obtain ⟨e,he,hV⟩:=physicalTypeIIRightCoupling_unique_sign q hq hq1 (h+1) (by omega) a b c d hbal t v hv hvn
  obtain ⟨f,hf,hC⟩:=physicalTypeIICalibratedRight_phase q hq hq1 h a b c d hbal t
  have hp:=physicalTypeIICalibratedRight_first_boundary_pos q hq hq1 h a b c d hbal t
  rw [hV] at hvb
  rw [hC] at hp
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul] at hvb hp
  have hef : e=f := by rcases he with rfl|rfl <;> rcases hf with rfl|rfl <;> first | rfl | nlinarith
  rw [hV,hC,hef]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIICalibratedRight_first_boundary_pos

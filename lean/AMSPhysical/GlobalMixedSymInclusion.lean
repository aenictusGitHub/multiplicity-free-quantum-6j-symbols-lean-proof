import MixedSymHighestBoundary
import TensorWeightedBilinIntrinsic
import QuantumTripleLeftTensorMetric
import HighestLineEmbedding
import PhysicalTripleIntrinsicMetrics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalMixedSymInclusion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s c : ℕ) :=
  (TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin (h+2)) p)
    (quantumOccupationSpace ℝ (Fin (h+2)) s)
    (quantumOccupationSpace ℝ (Fin (h+2)) c)).toLinearMap.comp
      (TensorProduct.map (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) c →ₗ[ℝ] _))

theorem globalMixedSymInclusion_left_inverse (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) :
    Function.LeftInverse (globalMixedSymProjection q hq hq1 h p s c)
      (globalMixedSymInclusion q hq hq1 h p s c) := by
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul v w =>
    change TensorProduct.map (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection
      LinearMap.id ((TensorProduct.assoc ℝ _ _ _).symm
        ((TensorProduct.assoc ℝ _ _ _) (v.val ⊗ₜ[ℝ] w)))=v ⊗ₜ[ℝ] w
    rw [LinearEquiv.symm_apply_apply,TensorProduct.map_tmul,LinearMap.id_apply,
      CompactHighestRealization.channelProjection_subtype]

theorem globalMixedSymInclusion_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s c : ℕ) :
    Function.Injective (globalMixedSymInclusion q hq hq1 h p s c) :=
  (globalMixedSymInclusion_left_inverse q hq hq1 h p s c).injective

theorem globalMixedSymInclusion_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (z : UqTypeA q (h+1))
    (v : (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (h+2)) c) :
    globalMixedSymInclusion q hq hq1 h p s c (globalMixedSymRepresentation q hq hq1 h p s c z v) =
      typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s c z
        (globalMixedSymInclusion q hq hq1 h p s c v) := by
  have hT:=typeA_intertwiner_tensor q (ne_of_gt hq) (h+1)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelAction
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype LinearMap.id
    (by intro z x;rfl) (by intro z x;rfl) z v
  refine (congrArg (TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin (h+2)) p)
    (quantumOccupationSpace ℝ (Fin (h+2)) s)
    (quantumOccupationSpace ℝ (Fin (h+2)) c)) hT).trans ?_
  exact typeA_associator_intertwines q (ne_of_gt hq) (h+1)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) s)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c) z _

theorem globalMixedSymVertex_inclusion_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :
    globalMixedSymInclusion q hq hq1 h p s c
      (globalMixedSymVertex q hq hq1 h p s c hs
        (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)))) =
      (globalTypeILeftVector q hq hq1 h p s c 0 hs).val := by
  have he:=globalMixedSymVertex_highest_factor q hq hq1 h p s c hs 0
  unfold globalAMSMixedIn at he
  simp only [Nat.mul_zero,pow_zero,one_smul,globalMixedPairClebsch_zero] at he
  have hA:=congrArg (TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin (h+2)) p)
    (quantumOccupationSpace ℝ (Fin (h+2)) s)
    (quantumOccupationSpace ℝ (Fin (h+2)) c)) he
  change globalMixedSymInclusion q hq hq1 h p s c
    (globalMixedSymVertex q hq hq1 h p s c hs
      (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)))) =
    (TensorProduct.assoc ℝ
      (quantumOccupationSpace ℝ (Fin (h+2)) p)
      (quantumOccupationSpace ℝ (Fin (h+2)) s)
      (quantumOccupationSpace ℝ (Fin (h+2)) c))
      ((TensorProduct.assoc ℝ
        (quantumOccupationSpace ℝ (Fin (h+2)) p)
        (quantumOccupationSpace ℝ (Fin (h+2)) s)
        (quantumOccupationSpace ℝ (Fin (h+2)) c)).symm
        (globalTypeILeftVector q hq hq1 h p s c 0 hs).val) at hA
  rw [LinearEquiv.apply_symm_apply] at hA
  exact hA

theorem globalMixedSymInclusion_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ)
    (v w : (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (h+2)) c) :
    physicalTripleBilin q (h+1) p s c (globalMixedSymInclusion q hq hq1 h p s c v)
      (globalMixedSymInclusion q hq hq1 h p s c w) =
      LinearMap.BilinForm.tmul
        (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
        (occupationCompactBilin q (h+1) c) v w := by
  unfold globalMixedSymInclusion
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [physicalTriple_assoc_isometry]
  rw [physicalLeftTripleBilin_eq_intrinsic]
  exact tensorBilin_isometry
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
    (occupationCompactBilin q (h+1) c) (mixedTensorBilin q (h+1) p s)
    (occupationCompactBilin q (h+1) c)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
    LinearMap.id (by intro x y;rfl) (by intro x y;rfl) v w

theorem globalMixedSymVertex_highest_norm (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :
    LinearMap.BilinForm.tmul
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
      (occupationCompactBilin q (h+1) c)
      (globalMixedSymVertex q hq hq1 h p s c hs
        (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))
      (globalMixedSymVertex q hq hq1 h p s c hs
        (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))=1 := by
  have hIsom:=globalMixedSymInclusion_isometry q hq hq1 h p s c
    (globalMixedSymVertex q hq hq1 h p s c hs
      (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))
    (globalMixedSymVertex q hq hq1 h p s c hs
      (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))
  have hHighest:=globalMixedSymVertex_inclusion_highest q hq hq1 h p s c hs
  exact hIsom.symm.trans ((congrArg (fun v=>physicalTripleBilin q (h+1) p s c v v) hHighest).trans
    (physicalTypeILeftCoupling_unit q hq hq1 (h+1) (by omega) p s 0 c (by omega) (Or.inl rfl)
      (globalTypeILeftCupIndex p s c 0 hs)))

end AMSPhysical
#print axioms AMSPhysical.globalMixedSymInclusion_intertwines
#print axioms AMSPhysical.globalMixedSymVertex_inclusion_highest

import SymMixedHighestBoundary
import PhysicalTripleIntrinsicMetrics
import HighestSpaceMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalSymMixedInclusion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a p s : ℕ) :=
  TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
    (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s 0)

theorem globalSymMixedInclusion_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a p s : ℕ) :
    Function.Injective (globalSymMixedInclusion q hq hq1 h a p s) := by
  have hR : Function.Injective (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s 0) := by
    intro v w he
    apply ((globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).transport (ne_of_gt hq)
      (globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s 0)).injective
    exact Subtype.ext he
  exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id hR

theorem globalSymMixedInclusion_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ) (z : UqTypeA q (h+1))
    (v : quantumOccupationSpace ℝ (Fin (h+2)) a ⊗[ℝ]
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel) :
    globalSymMixedInclusion q hq hq1 h a p s (globalSymMixedRepresentation q hq hq1 h a p s z v) =
      typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a s p z
        (globalSymMixedInclusion q hq hq1 h a p s v) := by
  exact typeA_intertwiner_tensor q (ne_of_gt hq) (h+1)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelAction
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a)
    (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) s p)
    LinearMap.id (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s 0)
    (by intro z x;rfl) (globalReverseMixedPairClebsch_intertwines q hq hq1 (h+1) (by omega) p s 0) z v

theorem globalSymMixedInclusion_mem_range (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (h+2)) a ⊗[ℝ]
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel) :
    globalSymMixedInclusion q hq hq1 h a p s v ∈
      LinearMap.range (TensorProduct.map
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype) := by
  refine ⟨TensorProduct.map LinearMap.id
    ((globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).transport (ne_of_gt hq)
      (globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s 0)).toLinearMap v,?_⟩
  rw [tensorRight_map_comp]
  rfl

theorem globalSymMixedInclusion_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (h+2)) a ⊗[ℝ]
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel) :
    physicalTripleBilin q (h+1) a s p (globalSymMixedInclusion q hq hq1 h a p s v)
      (globalSymMixedInclusion q hq hq1 h a p s w) =
      LinearMap.BilinForm.tmul (occupationCompactBilin q (h+1) a)
        (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair v w := by
  rw [physicalTripleBilin_eq_intrinsic_right]
  exact tensorBilin_isometry (occupationCompactBilin q (h+1) a)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
    (occupationCompactBilin q (h+1) a) (reverseMixedTensorBilin q (h+1) s p)
    LinearMap.id (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s 0)
    (by intro x y;rfl) (globalReverseMixedPairClebsch_isometry q hq hq1 (h+1) (by omega) p s 0) v w

theorem globalSymMixedVertex_highest_norm (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :
    LinearMap.BilinForm.tmul (occupationCompactBilin q (h+1) a)
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))=1 := by
  have hIsom:=globalSymMixedInclusion_isometry q hq hq1 h a p s
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
  exact hIsom.symm.trans ((globalSharedTypeIRightTree_isometry q hq hq1 h a p s d hbal hs 0 _ _).trans
    (symmetricHighestRealization q hq hq1 (h+1) d).highestNorm)

end AMSPhysical
#print axioms AMSPhysical.globalSymMixedInclusion_intertwines
#print axioms AMSPhysical.globalSymMixedVertex_highest_norm

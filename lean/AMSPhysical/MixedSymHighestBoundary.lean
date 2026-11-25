import MixedZeroHighestFunctional
import PhysicalLeftHighestFirstPositive
import SymmetricEndpointCartan
import ProjectedHighestCartan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def occupationCoordinate (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] ℝ :=
  (Finsupp.lapply x.val).comp (quantumOccupationSpace ℝ (Fin (n+1)) L).subtype

theorem mixedSymHighestBoundary_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (z : occupationWeights (Fin (h+2)) c)
    (v : quantumOccupationTripleSpace (h+1) p s c) :
    occupationCoordinate (h+1) c z
      (tensorFirstFunctional (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)
        (globalMixedSymProjection q hq hq1 h p s c v)) =
      occupationTripleCoefficients (h+1) p s c v
        ((highestOccupation (h+1) p).val,(lowestOccupation (h+1) s).val,z.val) := by
  have he : (occupationCoordinate (h+1) c z).comp
      ((tensorFirstFunctional (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)).comp
        (globalMixedSymProjection q hq hq1 h p s c)) =
      (Finsupp.lapply ((highestOccupation (h+1) p).val,(lowestOccupation (h+1) s).val,z.val)).comp
        (occupationTripleCoefficients (h+1) p s c) := by
    apply (occupationTripleBasis (h+1) p s c).ext
    intro xyz
    simp only [LinearMap.comp_apply,Finsupp.lapply_apply]
    rw [occupationTripleCoefficients_basis,occupationTripleBasis_apply]
    change occupationCoordinate (h+1) c z (tensorFirstFunctional
      (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)
      (TensorProduct.map (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection
        LinearMap.id ((quantumOccupationBasis (K:=ℝ) p xyz.1 ⊗ₜ[ℝ]
          quantumOccupationBasis (K:=ℝ) s xyz.2.1) ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) c xyz.2.2))) = _
    rw [TensorProduct.map_tmul,LinearMap.id_apply,tensorFirstFunctional_tmul,map_smul,
      mixedZeroHighestFunctional_projection,occupationTensorCoefficients_basis]
    simp only [occupationCoordinate,LinearMap.comp_apply,Finsupp.lapply_apply,Submodule.subtype_apply,
      quantumOccupationBasis_coe,Finsupp.single_apply,smul_eq_mul,occupationTripleEmbedding]
    split_ifs <;> simp_all [Prod.ext_iff]
  exact DFunLike.congr_fun he v

theorem mixedSymVertex_projected_cartan (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) (i : Fin (h+1)) :
    typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c i 2
      (tensorFirstFunctional (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)
        (globalMixedSymVertex q hq hq1 h p s c hs
          (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))) =
      q^(simpleOccupationWeight (h+1) (mixedBoundaryOccupation (h+1) c (c-s) (by omega)).val i) •
      (tensorFirstFunctional (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)
        (globalMixedSymVertex q hq hq1 h p s c hs
          (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))) := by
  rw [symmetricEndpointCartan (h+1) (by omega) p s c hs]
  exact projected_highest_Cartan q (ne_of_gt hq) (h+1) _ _
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).onChannel
    (symmetricHighestRealization q hq hq1 (h+1) (p+c-s))
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)
    (globalMixedSymVertex q hq hq1 h p s c hs)
    (globalMixedSymVertex_intertwines q hq hq1 h p s c hs) i

/-- The common intrinsic boundary is positive for the actual outer
mixed–symmetric vertex. The sum over the symmetric input reduces to its
single Cartan occupation, and the latter is the positive cup boundary. -/
theorem globalMixedSymVertex_highest_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :
    0 < occupationAugmentation (h+1) c
      (tensorFirstFunctional (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)
        (globalMixedSymVertex q hq hq1 h p s c hs
          (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))) := by
  rw [occupationAugmentation_joint_cartan q hq hq1 (h+1) c
    (mixedBoundaryOccupation (h+1) c (c-s) (by omega)) _
    (mixedSymVertex_projected_cartan q hq hq1 h p s c hs)]
  change 0 < occupationCoordinate (h+1) c (mixedBoundaryOccupation (h+1) c (c-s) (by omega))
    (tensorFirstFunctional (mixedZeroHighestFunctional q hq hq1 (h+1) (by omega) p s)
      (globalMixedSymProjection q hq hq1 h p s c
        (globalTypeILeftFullTree q hq hq1 h p s c hs
          (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))))))
  rw [mixedSymHighestBoundary_projection,globalTypeILeftFullTree_highest]
  have hp : ((highestOccupation (h+1) p).val,(lowestOccupation (h+1) s).val,
      (mixedBoundaryOccupation (h+1) c (c-s) (by omega)).val) =
      quantumCupBoundaryPoint (h+1) (p:ℤ) 0 (c:ℤ) 0 s := by
    simp [highestOccupation,lowestOccupation,mixedBoundaryOccupation,quantumCupBoundaryPoint,
      Nat.sub_sub_self hs,Nat.cast_sub hs]
  rw [hp]
  exact physicalTypeILeftCoupling_zero_highest_first_pos q hq hq1 (h+1) (by omega) p s 0 c hs (Or.inl rfl)

end AMSPhysical
#print axioms AMSPhysical.mixedSymVertex_projected_cartan
#print axioms AMSPhysical.globalMixedSymVertex_highest_boundary_pos

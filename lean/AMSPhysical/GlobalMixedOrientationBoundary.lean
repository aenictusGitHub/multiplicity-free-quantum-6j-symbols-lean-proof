import PureMixedHighest
import HighestFunctionalTransport
import MixedOrientationWordBoundary
import QuantumReverseFusionRealization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationReflection_highest (n L : ℕ) :
    occupationReflection n L (highestOccupation n L)=lowestOccupation n L := by
  apply Subtype.ext
  funext i
  have hi : i.rev=(0:Fin (n+1)) ↔ i=Fin.last n := by
    simp only [Fin.ext_iff,Fin.val_rev,Fin.val_zero,Fin.val_last]
    have hib:=i.isLt
    omega
  simp only [occupationReflection,highestOccupation,lowestOccupation,Pi.single_apply]
  simp only [eq_comm (a:=(0:Fin (n+1))),eq_comm (a:=Fin.last n),hi]

theorem occupationReflection_lowest (n L : ℕ) :
    occupationReflection n L (lowestOccupation n L)=highestOccupation n L := by
  rw [← occupationReflection_highest,occupationReflection_involutive]

theorem normalizedReverseMixedFusionHighest_zero (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (p s : ℕ) :
    normalizedReverseMixedFusionHighestAt q n s p ⟨0,by omega⟩ =
      quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) p (highestOccupation n p) := by
  have h : normalizedReverseMixedFusionHighestAt q n s p ⟨0,by omega⟩ =
      mixedReflection n s p (normalizedMixedFusionHighestAt q n s p ⟨0,by omega⟩) := by
    unfold normalizedReverseMixedFusionHighestAt normalizedMixedFusionHighestAt reverseMixedFusionHighestAt
    rw [map_smul]
  rw [h,normalizedMixedFusionHighest_zero q hq n hn]
  simp only [mixedReflection,TensorProduct.congr_tmul,quantumOccupationReflection_basis,
    occupationReflection_highest,occupationReflection_lowest]

def globalReverseMixedPairRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) : CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) (s+r) ⊗[ℝ]
        quantumOccupationSpace ℝ (Fin (n+1)) (p+r)) (mixedHighestDynkin n p s) where
  action := typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (s+r) (p+r)
  pairing := reverseMixedTensorBilin q n (s+r) (p+r)
  highest := normalizedReverseMixedFusionHighestAt q n (s+r) (p+r) (globalMixedPairIndex s p r)
  compact := typeAReverseMixedTensor_compact q hq hq1 n (s+r) (p+r)
  symmetric := reverseMixedTensorBilin_symm q n (s+r) (p+r)
  definite := reverseMixedTensorBilin_definite q hq n (s+r) (p+r)
  highestE := (reverseMixedFusionHighestRealization q hq hq1 n hn (s+r) (p+r) (globalMixedPairIndex s p r)).highestE
  highestK := by
    intro i
    simpa only [globalMixedPairIndex,Nat.add_sub_cancel] using
      (reverseMixedFusionHighestRealization q hq hq1 n hn (s+r) (p+r) (globalMixedPairIndex s p r)).highestK i
  highestNorm := normalizedReverseMixedFusionHighestAt_norm_one q hq n hn (s+r) (p+r) (globalMixedPairIndex s p r)

/-- The all-first boundary functionals have a positive, explicit ratio on
the entire common mixed irrep, not just a selected weight vector. -/
theorem globalMixedOrientation_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s : ℕ)
    (x : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    reverseMixedFirstBoundaryFunctional n p s
      ((globalMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
        (globalReverseMixedPairRealization q hq hq1 n hn p s 0) x).val =
      q^((p:ℤ)*(s:ℤ))*mixedFirstBoundaryFunctional n p s x.val := by
  refine CompactHighestRealization.transport_functional_of_lowering (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s 0)
    (globalReverseMixedPairRealization q hq hq1 n hn p s 0)
    (mixedFirstBoundaryFunctional n p s) (reverseMixedFirstBoundaryFunctional n p s)
    _ ?_ x
  intro w
  change reverseMixedFirstBoundaryFunctional n p s
    (typeALoweredVector q n (typeAReverseMixedTensor q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n s p)
      (normalizedReverseMixedFusionHighestAt q n s p ⟨0,by omega⟩) w) = _
  rw [normalizedReverseMixedFusionHighest_zero q hq n hn]
  change _ = q^((p:ℤ)*(s:ℤ))*mixedFirstBoundaryFunctional n p s
    (typeALoweredVector q n (typeAMixedTensor q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n p s)
      (normalizedMixedFusionHighestAt q n p s ⟨0,by omega⟩) w)
  rw [normalizedMixedFusionHighest_zero q hq n hn]
  exact mixed_orientation_word_boundary q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn p s w

end AMSPhysical
#print axioms AMSPhysical.globalMixedOrientation_boundary

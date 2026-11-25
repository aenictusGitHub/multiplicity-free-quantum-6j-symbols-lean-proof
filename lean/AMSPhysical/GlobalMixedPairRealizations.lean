import GlobalScalarHighestTransport
import GlobalMixedCreationCoherence
import QuantumCreationSpectralScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalMixedPairIndex (p s r : ℕ) : MixedFusionIndex (p+r) (s+r) := ⟨r,by omega⟩

def globalMixedPairRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r : ℕ) : CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) (p+r) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (s+r))
      (mixedHighestDynkin n p s) where
  action := typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (p+r) (s+r)
  pairing := mixedTensorBilin q n (p+r) (s+r)
  highest := normalizedMixedFusionHighestAt q n (p+r) (s+r) (globalMixedPairIndex p s r)
  compact := typeAMixedTensor_compact q hq hq1 n (p+r) (s+r)
  symmetric := mixedTensorBilin_symm q n (p+r) (s+r)
  definite := mixedTensorBilin_definite q hq n (p+r) (s+r)
  highestE := (mixedFusionHighestRealization q hq hq1 n hn (p+r) (s+r) (globalMixedPairIndex p s r)).highestE
  highestK := by
    intro i
    simpa only [globalMixedPairIndex,Nat.add_sub_cancel] using
      (mixedFusionHighestRealization q hq hq1 n hn (p+r) (s+r) (globalMixedPairIndex p s r)).highestK i
  highestNorm := normalizedMixedFusionHighestAt_norm_one q hq n hn (p+r) (s+r) (globalMixedPairIndex p s r)

theorem globalMixedPair_creation_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r : ℕ) :
    mixedFiniteCreation q n (p+r) (s+r) (globalMixedPairRealization q hq hq1 n hn p s r).highest =
      mixedCreationUnitScale q n (p+r) (s+r) (globalMixedPairIndex p s r) •
        (globalMixedPairRealization q hq hq1 n hn p s (r+1)).highest := by
  exact mixedFiniteCreation_normalized_highest q hq hq1 n hn (p+r) (s+r) (globalMixedPairIndex p s r)

theorem globalMixedPair_creation_transport (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r : ℕ) (x : (globalMixedPairRealization q hq hq1 n hn p s r).channel) :
    mixedFiniteCreation q n (p+r) (s+r) x.val =
      mixedCreationUnitScale q n (p+r) (s+r) (globalMixedPairIndex p s r) •
        ((globalMixedPairRealization q hq hq1 n hn p s r).transport (ne_of_gt hq)
          (globalMixedPairRealization q hq hq1 n hn p s (r+1)) x).val := by
  exact CompactHighestRealization.intertwiner_scalar_highest (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s r)
    (globalMixedPairRealization q hq hq1 n hn p s (r+1))
    (mixedFiniteCreation q n (p+r) (s+r)) _
    (mixedFiniteCreation_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (p+r) (s+r))
    (globalMixedPair_creation_highest q hq hq1 n hn p s r) x

theorem mixedCreationUnitScale_square (q : ℝ) (hq : 0<q) (n b c : ℕ) (r : MixedFusionIndex b c) :
    (mixedCreationUnitScale q n b c r)^2=mixedCreationSpectralScalar q n b c r.val := by
  have hN:=mixedCouplingNormClosed_pos q hq n (b-r.val) (c-r.val) r.val
  have hT:=mixedCouplingNormClosed_pos q hq n (b-r.val) (c-r.val) (r.val+1)
  have hs:=Real.sq_sqrt hN.le
  have ht:=Real.sq_sqrt hT.le
  have hr:=r.isLt
  rw [← mixedCreationSpectralScalar_norm_ratio q hq n b c r.val (by omega) (by omega)]
  unfold mixedCreationUnitScale
  rw [div_pow,mul_pow,ht,hs]
  ring

theorem mixedCreationUnitScale_eq_sqrt (q : ℝ) (hq : 0<q) (n b c : ℕ) (r : MixedFusionIndex b c) :
    mixedCreationUnitScale q n b c r =
      Real.sqrt (mixedCreationSpectralScalar q n b c r.val) := by
  rw [← mixedCreationUnitScale_square q hq]
  exact (Real.sqrt_sq (mixedCreationUnitScale_pos q hq n b c r).le).symm

end AMSPhysical
#print axioms AMSPhysical.globalMixedPair_creation_transport
#print axioms AMSPhysical.mixedCreationUnitScale_eq_sqrt

import GlobalHighestCarrierCoherence
import QuantumMixedFusionRealization
import QuantumMixedCreationHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedCreationUnitScale (q : ℝ) (n l m : ℕ) (r : MixedFusionIndex l m) : ℝ :=
  q^(-(l:ℤ)-(r.val:ℤ)) *
    Real.sqrt (mixedCouplingNormClosed q n (l-r.val) (m-r.val) (r.val+1)) /
    Real.sqrt (mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val)

theorem mixedCreationUnitScale_pos (q : ℝ) (hq : 0<q) (n l m : ℕ) (r : MixedFusionIndex l m) :
    0 < mixedCreationUnitScale q n l m r :=
  div_pos (mul_pos (zpow_pos hq _)
    (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n _ _ _)))
    (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n _ _ _))

theorem mixedFiniteCreation_normalized_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedFiniteCreation q n l m (normalizedMixedFusionHighestAt q n l m r) =
      mixedCreationUnitScale q n l m r • normalizedMixedFusionHighestAt q n (l+1) (m+1)
        (mixedFusionIndexSucc l m r) := by
  unfold normalizedMixedFusionHighestAt
  rw [map_smul,mixedFiniteCreation_highest q hq hq1 n hn,smul_smul,smul_smul]
  simp only [mixedFusionIndexSucc,Nat.add_sub_add_right]
  congr 1
  unfold mixedCreationUnitScale
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n (l-r.val) (m-r.val) (r.val+1)))]

def mixedCreationTargetRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
      (mixedHighestDynkin n (l-r.val) (m-r.val)) where
  action := typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1)
  pairing := mixedTensorBilin q n (l+1) (m+1)
  highest := normalizedMixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r)
  compact := typeAMixedTensor_compact q hq hq1 n (l+1) (m+1)
  symmetric := mixedTensorBilin_symm q n (l+1) (m+1)
  definite := mixedTensorBilin_definite q hq n (l+1) (m+1)
  highestE := (mixedFusionHighestRealization q hq hq1 n hn (l+1) (m+1) (mixedFusionIndexSucc l m r)).highestE
  highestK := by
    intro i
    simpa only [mixedFusionIndexSucc,Nat.add_sub_add_right] using
      (mixedFusionHighestRealization q hq hq1 n hn (l+1) (m+1) (mixedFusionIndexSucc l m r)).highestK i
  highestNorm := normalizedMixedFusionHighestAt_norm_one q hq n hn (l+1) (m+1) (mixedFusionIndexSucc l m r)

/-- On the ENTIRE actual irreducible channel, physical creation is the
canonical highest transport times one explicitly positive scalar. -/
theorem mixedFiniteCreation_channel_transport (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (x : (mixedFusionHighestRealization q hq hq1 n hn l m r).channel) :
    mixedFiniteCreation q n l m x.val = mixedCreationUnitScale q n l m r •
      ((mixedFusionHighestRealization q hq hq1 n hn l m r).transport (ne_of_gt hq)
        (mixedCreationTargetRealization q hq hq1 n hn l m r) x).val := by
  let X:=mixedFusionHighestRealization q hq hq1 n hn l m r
  let Y:=mixedCreationTargetRealization q hq hq1 n hn l m r
  let f := (mixedFiniteCreation q n l m).comp X.channel.subtype
  let g := mixedCreationUnitScale q n l m r •
    (Y.channel.subtype.comp (X.transport (ne_of_gt hq) Y).toLinearMap)
  have he : f=g := by
    apply cyclic_intertwiner_unique
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (W:=quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
      X.action Y.action X.highest f g
    · intro z v
      exact mixedFiniteCreation_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z v.val
    · intro z v
      change mixedCreationUnitScale q n l m r •
        ((X.transport (ne_of_gt hq) Y) (X.channelAction z v)).val =
        Y.action z (mixedCreationUnitScale q n l m r • ((X.transport (ne_of_gt hq) Y) v).val)
      rw [map_smul]
      exact congrArg (fun v => mixedCreationUnitScale q n l m r • v)
        (X.transport_intertwines (ne_of_gt hq) Y z v)
    · change mixedFiniteCreation q n l m (normalizedMixedFusionHighestAt q n l m r) =
        mixedCreationUnitScale q n l m r •
          ((X.transport (ne_of_gt hq) Y) ⟨X.highest,algebraCyclicSpan_self _ _⟩).val
      rw [X.transport_highest]
      exact mixedFiniteCreation_normalized_highest q hq hq1 n hn l m r
  exact DFunLike.congr_fun he x

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreation_channel_transport

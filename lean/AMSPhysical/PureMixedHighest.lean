import GlobalMixedPairRealizations
import QuantumReverseNormalizedHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem zeroOccupation_unique (n : ℕ) (x : occupationWeights (Fin (n+1)) 0) : x=highestOccupation n 0 := by
  apply Subtype.ext
  funext i
  have hl:=x.property.1 i
  have hu:=occupationWeight_bound 0 x i
  simp only [highestOccupation,Pi.single_apply,Nat.cast_zero,ite_self]
  omega

theorem mixedCouplingNormClosed_zero (q : ℝ) (hq : 0<q) (n p s : ℕ) :
    mixedCouplingNormClosed q n p s 0=1 := by
  unfold mixedCouplingNormClosed
  simp only [Nat.cast_zero,mul_zero,zpow_zero,qfactorial_zero,one_mul,Nat.add_zero,Nat.zero_add]
  exact div_self (mul_ne_zero (mul_ne_zero (qfactorial_ne_zero q hq p) (qfactorial_ne_zero q hq s))
    (qfactorial_ne_zero q hq (p+n+s)))

theorem normalizedMixedFusionHighest_zero (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (p s : ℕ) :
    normalizedMixedFusionHighestAt q n p s ⟨0,by omega⟩ =
      quantumOccupationBasis (K:=ℝ) p (highestOccupation n p) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s) := by
  classical
  unfold normalizedMixedFusionHighestAt
  simp only [Fin.val_mk,Nat.sub_zero,mixedCouplingNormClosed_zero q hq,Real.sqrt_one,inv_one,one_smul]
  unfold mixedFusionHighestAt mixedFusionHighest
  letI : Unique (occupationWeights (Fin (n+1)) 0) :=
    { default:=highestOccupation n 0,uniq:=zeroOccupation_unique n }
  simp only [Fin.val_mk,Nat.sub_zero,Finset.univ_unique,Finset.sum_singleton]
  change mixedHighestCoefficient q n 0 s (highestOccupation n 0) • _ = _
  rw [mixedHighestCoefficient_highest q hq n 0 s hn,one_smul]
  have hp : shiftedOccupationWithin n p 0 (by omega) 0 (highestOccupation n 0)=highestOccupation n p := by
    apply Subtype.ext
    funext i
    simp [shiftedOccupationWithin,highestOccupation,Pi.single_apply]
  have hs : shiftedOccupationWithin n s 0 (by omega) (Fin.last n) (highestOccupation n 0)=lowestOccupation n s := by
    apply Subtype.ext
    funext i
    simp [shiftedOccupationWithin,highestOccupation,lowestOccupation,Pi.single_apply]
  rw [zeroOccupation_unique n (default : occupationWeights (Fin (n+1)) 0),hp,hs]

theorem globalMixedPairRealization_zero_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s : ℕ) :
    (globalMixedPairRealization q hq hq1 n hn p s 0).highest =
      quantumOccupationBasis (K:=ℝ) p (highestOccupation n p) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s) :=
  normalizedMixedFusionHighest_zero q hq n hn p s

end AMSPhysical
#print axioms AMSPhysical.normalizedMixedFusionHighest_zero

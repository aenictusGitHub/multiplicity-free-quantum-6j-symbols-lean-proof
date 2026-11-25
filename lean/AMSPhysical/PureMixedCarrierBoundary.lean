import ActualAMSBoundary
import OccupationTensorHighestSlices
import CompactTrivialHighest
import QuantumTypeAInvariantTensor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem CompactHighestRealization.weight_zero_invariant {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (hq : q≠0) (X : CompactHighestRealization q n V lam) (hLam : ∀ i,lam i=0) :
    ∀ z,X.action z X.highest=typeAQuantumCounit q n z • X.highest :=
  compact_weight_zero_highest_invariant q hq n X.action X.pairing X.compact X.definite X.highest
    X.highestE (by intro i;rw [X.highestK,hLam i,zpow_zero,one_smul])

theorem actualPureMixed_opposite_insertion (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (s : ℕ) (v : (actualOppositeCarrier q hq hq1 n hn s).space) :
    ((actualOppositeCarrier q hq hq1 n hn s).mapTo (ne_of_gt hq)
      (actualMixedCarrier q hq hq1 n hn 0 s) v).val =
      quantumOccupationBasis (K:=ℝ) 0 (highestOccupation n 0) ⊗ₜ[ℝ] v := by
  let O:=actualOppositeCarrier q hq hq1 n hn s
  let M:=actualMixedCarrier q hq hq1 n hn 0 s
  let X:=globalMixedPairRealization q hq hq1 n hn 0 s 0
  let F:=X.channel.subtype.comp (O.mapTo (ne_of_gt hq) M)
  let J : O.space →ₗ[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) 0 ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) s :=
    tensorWithLeftVector (quantumOccupationBasis (K:=ℝ) 0 (highestOccupation n 0))
  have he : F=J := by
    apply O.frame.full_intertwiner_unique O.complete X.action F J
    · intro z v
      exact congrArg Subtype.val (O.mapTo_intertwines (ne_of_gt hq) M z v)
    · exact typeA_tensor_invariant_left q (ne_of_gt hq) n
        (symmetricHighestRealization q hq hq1 n 0).action O.frame.action _
        ((symmetricHighestRealization q hq hq1 n 0).weight_zero_invariant (ne_of_gt hq)
          (by intro i;simp [mixedHighestDynkin]))
    · change ((O.mapTo (ne_of_gt hq) M) O.frame.highest).val=J O.frame.highest
      rw [O.mapTo_highest]
      exact globalMixedPairRealization_zero_highest q hq hq1 n hn 0 s
  exact DFunLike.congr_fun he v

theorem actualPureMixed_symmetric_insertion (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p : ℕ) (v : (actualSymmetricCarrier q hq hq1 n p).space) :
    ((actualSymmetricCarrier q hq hq1 n p).mapTo (ne_of_gt hq)
      (actualMixedCarrier q hq hq1 n hn p 0) v).val =
      v ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) 0 (lowestOccupation n 0) := by
  let S:=actualSymmetricCarrier q hq hq1 n p
  let M:=actualMixedCarrier q hq hq1 n hn p 0
  let X:=globalMixedPairRealization q hq hq1 n hn p 0 0
  let F:=X.channel.subtype.comp (S.mapTo (ne_of_gt hq) M)
  let J : S.space →ₗ[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) p ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) 0 :=
    tensorWithRightVector (quantumOccupationBasis (K:=ℝ) 0 (lowestOccupation n 0))
  have he : F=J := by
    apply S.frame.full_intertwiner_unique S.complete X.action F J
    · intro z v
      exact congrArg Subtype.val (S.mapTo_intertwines (ne_of_gt hq) M z v)
    · exact typeA_tensor_invariant_right q (ne_of_gt hq) n S.frame.action
        (oppositeHighestRealization q hq hq1 n 0).action _
        ((oppositeHighestRealization q hq hq1 n 0).weight_zero_invariant (ne_of_gt hq)
          (by intro i;simp [mixedHighestDynkin]))
    · change ((S.mapTo (ne_of_gt hq) M) S.frame.highest).val=J S.frame.highest
      rw [S.mapTo_highest]
      exact globalMixedPairRealization_zero_highest q hq hq1 n hn p 0
  exact DFunLike.congr_fun he v

theorem actualPureMixed_opposite_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (s : ℕ) (v : (actualMixedCarrier q hq hq1 n hn 0 s).space) :
    mixedFirstBoundaryFunctional n 0 s v.val = occupationHighestFunctional n s
      ((actualMixedCarrier q hq hq1 n hn 0 s).mapTo (ne_of_gt hq)
        (actualOppositeCarrier q hq hq1 n hn s) v) := by
  have he:=actualPureMixed_opposite_insertion q hq hq1 n hn s
    ((actualMixedCarrier q hq hq1 n hn 0 s).mapTo (ne_of_gt hq)
      (actualOppositeCarrier q hq hq1 n hn s) v)
  have hRound:=DFunLike.congr_fun
    ((actualMixedCarrier q hq hq1 n hn 0 s).mapTo_comp (ne_of_gt hq)
      (actualOppositeCarrier q hq hq1 n hn s) (actualMixedCarrier q hq hq1 n hn 0 s)) v
  rw [ActualHighestCarrier.mapTo_self] at hRound
  simp only [LinearMap.comp_apply,LinearMap.id_apply] at hRound
  change _=v at hRound
  rw [hRound] at he
  rw [he]
  simp only [mixedFirstBoundaryFunctional,LinearMap.comp_apply,tensorFirstFunctional_tmul,
    occupationHighestFunctional_highest,one_smul]

theorem actualPureMixed_symmetric_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p : ℕ) (v : (actualMixedCarrier q hq hq1 n hn p 0).space) :
    mixedFirstBoundaryFunctional n p 0 v.val = occupationHighestFunctional n p
      ((actualMixedCarrier q hq hq1 n hn p 0).mapTo (ne_of_gt hq)
        (actualSymmetricCarrier q hq hq1 n p) v) := by
  have he:=actualPureMixed_symmetric_insertion q hq hq1 n hn p
    ((actualMixedCarrier q hq hq1 n hn p 0).mapTo (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 n p) v)
  have hRound:=DFunLike.congr_fun
    ((actualMixedCarrier q hq hq1 n hn p 0).mapTo_comp (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 n p) (actualMixedCarrier q hq hq1 n hn p 0)) v
  rw [ActualHighestCarrier.mapTo_self] at hRound
  simp only [LinearMap.comp_apply,LinearMap.id_apply] at hRound
  change _=v at hRound
  rw [hRound] at he
  rw [he]
  have hUnit : occupationHighestFunctional n 0 (quantumOccupationBasis (K:=ℝ) 0 (lowestOccupation n 0))=1 := by
    rw [zeroOccupation_unique n (lowestOccupation n 0)]
    exact occupationHighestFunctional_highest n 0
  simp only [mixedFirstBoundaryFunctional,LinearMap.comp_apply,tensorFirstFunctional_tmul,
    map_smul,smul_eq_mul,hUnit,mul_one]

end AMSPhysical
#print axioms AMSPhysical.actualPureMixed_opposite_boundary
#print axioms AMSPhysical.actualPureMixed_symmetric_boundary

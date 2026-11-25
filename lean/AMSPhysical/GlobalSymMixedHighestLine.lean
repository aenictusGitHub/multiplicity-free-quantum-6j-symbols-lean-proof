import GlobalSymMixedInclusion
import HighestLineEmbedding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option Elab.async false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

abbrev globalSymMixedHighestSpace (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a p s : ℕ) :=
  typeAHighestSpace
    (V:=quantumOccupationSpace ℝ (Fin (h+2)) a ⊗[ℝ]
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel)
    q (h+1) (globalSymMixedRepresentation q hq hq1 h a p s) (mixedHighestDynkin (h+1) (a+p-s) 0)

def globalSymMixedHighestMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a p s : ℕ) :
    globalSymMixedHighestSpace q hq hq1 h a p s →ₗ[ℝ]
      physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a s 0 p where
  toFun v := ⟨globalSymMixedInclusion q hq hq1 h a p s v.val,by
    obtain ⟨hE,hK⟩:=(mem_typeAHighestSpace q (h+1) _ _ v.val).mp v.property
    apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
    constructor
    · intro i
      change typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a s p (typeAAlgebraGenerator q (h+1) i 0) (globalSymMixedInclusion q hq hq1 h a p s v.val)=0
      rw [← globalSymMixedInclusion_intertwines q hq hq1 h a p s,hE,map_zero]
    · intro i
      change typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a s p (typeAAlgebraGenerator q (h+1) i 2) (globalSymMixedInclusion q hq hq1 h a p s v.val)=
          q^(mixedHighestDynkin (h+1) (a+p-s) 0 i) • globalSymMixedInclusion q hq hq1 h a p s v.val
      rw [← globalSymMixedInclusion_intertwines q hq hq1 h a p s,hK,map_smul]⟩
  map_add' v w := by apply Subtype.ext;exact (globalSymMixedInclusion q hq hq1 h a p s).map_add v.val w.val
  map_smul' b v := by apply Subtype.ext;exact (globalSymMixedInclusion q hq hq1 h a p s).map_smul b v.val

theorem globalSymMixedHighestMap_mem_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ) (hs : s≤a) (v : globalSymMixedHighestSpace q hq hq1 h a p s) :
    globalSymMixedHighestMap q hq hq1 h a p s v ∈
      physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a s 0 p (globalTypeIIRightCupIndex a p s 0 hs) := by
  change globalSymMixedInclusion q hq hq1 h a p s v.val ∈
    physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) a s p (physicalTypeIRightIndex a s 0 p (globalTypeIIRightCupIndex a p s 0 hs))
  rw [physicalTripleRightChannelGeneral_actual q hq hq1 (h+1) (by omega)]
  let S:=reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    (h+1) s p (physicalTypeIRightIndex a s 0 p (globalTypeIIRightCupIndex a p s 0 hs))
  let T:=(globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel
  have hST : S=T := by
    have hI : physicalTypeIRightIndex a s 0 p (globalTypeIIRightCupIndex a p s 0 hs)=
        globalMixedPairIndex s p 0 := by
      apply Fin.ext
      simp only [physicalTypeIRightIndex,globalTypeIIRightCupIndex,globalMixedPairIndex]
      omega
    dsimp only [S,T]
    rw [hI]
    exact (globalReverseMixedPairRealization_channel q hq hq1 (h+1) (by omega) p s 0).symm
  have hRange:=tensorRight_range_congr (A:=quantumOccupationSpace ℝ (Fin (h+2)) a) S T hST
  change globalSymMixedInclusion q hq hq1 h a p s v.val∈LinearMap.range (TensorProduct.map LinearMap.id S.subtype)
  rw [hRange]
  exact globalSymMixedInclusion_mem_range q hq hq1 h a p s v.val

theorem globalSymMixedHighestSpace_finrank_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ) (hs : s≤a) :
    Module.finrank ℝ (globalSymMixedHighestSpace q hq hq1 h a p s)=1 := by
  let U : Type := quantumOccupationSpace ℝ (Fin (h+2)) a ⊗[ℝ]
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel
  letI : AddCommGroup U := inferInstance
  letI : Module ℝ U := inferInstance
  let H : Submodule ℝ U := globalSymMixedHighestSpace q hq hq1 h a p s
  letI : AddCommGroup H := inferInstance
  letI : Module ℝ H := inferInstance
  let v : globalSymMixedHighestSpace q hq hq1 h a p s :=
    ⟨globalSymMixedVertex q hq hq1 h a p s (a+p-s) (by omega) hs
      (quantumOccupationBasis (K:=ℝ) (a+p-s) (highestOccupation (h+1) (a+p-s))),by
      apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
      constructor
      · intro i
        rw [← globalSymMixedVertex_intertwines q hq hq1 h a p s (a+p-s) (by omega) hs]
        have he:=(symmetricHighestRealization q hq hq1 (h+1) (a+p-s)).highestE i
        change typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          (h+1) (a+p-s) _ (quantumOccupationBasis (K:=ℝ) (a+p-s) (highestOccupation (h+1) (a+p-s)))=0 at he
        rw [he,map_zero]
      · intro i
        rw [← globalSymMixedVertex_intertwines q hq hq1 h a p s (a+p-s) (by omega) hs]
        have he:=(symmetricHighestRealization q hq hq1 (h+1) (a+p-s)).highestK i
        change typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          (h+1) (a+p-s) _ (quantumOccupationBasis (K:=ℝ) (a+p-s) (highestOccupation (h+1) (a+p-s)))=
            q^(mixedHighestDynkin (h+1) (a+p-s) 0 i) •
              quantumOccupationBasis (K:=ℝ) (a+p-s) (highestOccupation (h+1) (a+p-s)) at he
        rw [he,map_smul]⟩
  have hv : v≠0 := by
    intro he
    have hz:=congrArg Subtype.val he
    have hNorm:=globalSymMixedVertex_highest_norm q hq hq1 h a p s (a+p-s) (by omega) hs
    change v.val=0 at hz
    change LinearMap.BilinForm.tmul (occupationCompactBilin q (h+1) a)
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair v.val v.val=1 at hNorm
    rw [hz,map_zero] at hNorm
    norm_num at hNorm
  apply finrank_one_of_line_embedding
    (physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) a s 0 p (globalTypeIIRightCupIndex a p s 0 hs)) _
    (globalSymMixedHighestMap q hq hq1 h a p s) _
    (globalSymMixedHighestMap_mem_channel q hq hq1 h a p s hs) v hv
  · rw [← completeHighestRightAction_eigenspace_eq_channel q hq hq1 (h+1) (by omega)
      a s 0 p (by omega) (Or.inl rfl)]
    exact completeHighestRightAction_eigenspace_finrank q hq hq1 (h+1) (by omega)
      a s 0 p (by omega) (Or.inl rfl) (globalTypeIIRightCupIndex a p s 0 hs)
  · intro v w he
    apply Subtype.ext
    apply globalSymMixedInclusion_injective q hq hq1 h a p s
    exact congrArg Subtype.val he

end AMSPhysical
#print axioms AMSPhysical.globalSymMixedHighestSpace_finrank_one

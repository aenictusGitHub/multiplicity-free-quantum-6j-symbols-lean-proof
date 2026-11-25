import GlobalMixedSymInclusion
import HighestSpaceMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct


abbrev globalMixedSymHighestSpace (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s c : ℕ) :=
  typeAHighestSpace
    (V:=(globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (h+2)) c)
    q (h+1) (globalMixedSymRepresentation q hq hq1 h p s c) (mixedHighestDynkin (h+1) (p+c-s) 0)


def globalMixedSymHighestMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s c : ℕ) :
    globalMixedSymHighestSpace q hq hq1 h p s c →ₗ[ℝ]
      physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) p s 0 c where
  toFun v := ⟨globalMixedSymInclusion q hq hq1 h p s c v.val,by
    obtain ⟨hE,hK⟩:=(mem_typeAHighestSpace q (h+1) _ _ v.val).mp v.property
    apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
    constructor
    · intro i
      change typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) p s c (typeAAlgebraGenerator q (h+1) i 0) (globalMixedSymInclusion q hq hq1 h p s c v.val)=0
      rw [← globalMixedSymInclusion_intertwines q hq hq1 h p s c,hE,map_zero]
    · intro i
      change typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) p s c (typeAAlgebraGenerator q (h+1) i 2) (globalMixedSymInclusion q hq hq1 h p s c v.val)=
          q^(mixedHighestDynkin (h+1) (p+c-s) 0 i) • globalMixedSymInclusion q hq hq1 h p s c v.val
      rw [← globalMixedSymInclusion_intertwines q hq hq1 h p s c,hK,map_smul]⟩
  map_add' v w := by apply Subtype.ext;exact (globalMixedSymInclusion q hq hq1 h p s c).map_add v.val w.val
  map_smul' a v := by apply Subtype.ext;exact (globalMixedSymInclusion q hq hq1 h p s c).map_smul a v.val


theorem globalMixedSymHighestMap_mem_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) (v : globalMixedSymHighestSpace q hq hq1 h p s c) :
    globalMixedSymHighestMap q hq hq1 h p s c v ∈
      physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) p s 0 c (globalTypeILeftCupIndex p s c 0 hs) := by
  change globalMixedSymInclusion q hq hq1 h p s c v.val ∈
    physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) p s c (physicalTypeILeftIndex p s 0 c (globalTypeILeftCupIndex p s c 0 hs))
  rw [physicalTripleLeftChannelGeneral_actual q hq hq1 (h+1) (by omega)]
  let S:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    (h+1) p s (physicalTypeILeftIndex p s 0 c (globalTypeILeftCupIndex p s c 0 hs))
  let T:=(globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel
  have hST : S=T := by
    have hI : physicalTypeILeftIndex p s 0 c (globalTypeILeftCupIndex p s c 0 hs)=
        globalMixedPairIndex p s 0 := by apply Fin.ext;rfl
    dsimp only [S,T]
    rw [hI]
    exact (globalMixedPairRealization_channel q hq hq1 (h+1) (by omega) p s 0).symm
  refine ⟨TensorProduct.map T.subtype LinearMap.id v.val,?_,rfl⟩
  have hRange:=tensorLeft_range_congr (A:=quantumOccupationSpace ℝ (Fin (h+2)) c) S T hST
  change TensorProduct.map T.subtype LinearMap.id v.val∈LinearMap.range (TensorProduct.map S.subtype LinearMap.id)
  rw [hRange]
  exact ⟨v.val,rfl⟩


theorem globalMixedSymHighestSpace_finrank_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :
    Module.finrank ℝ (globalMixedSymHighestSpace q hq hq1 h p s c)=1 := by
  let U : Type := (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel ⊗[ℝ]
    quantumOccupationSpace ℝ (Fin (h+2)) c
  letI : AddCommGroup U := inferInstance
  letI : Module ℝ U := inferInstance
  let H : Submodule ℝ U := globalMixedSymHighestSpace q hq hq1 h p s c
  letI : AddCommGroup H := inferInstance
  letI : Module ℝ H := inferInstance
  let v : globalMixedSymHighestSpace q hq hq1 h p s c :=
    ⟨globalMixedSymVertex q hq hq1 h p s c hs
      (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))),
      by
        apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
        constructor
        · intro i
          rw [← globalMixedSymVertex_intertwines q hq hq1 h p s c hs]
          have he:=(symmetricHighestRealization q hq hq1 (h+1) (p+c-s)).highestE i
          change typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
            (h+1) (p+c-s) _ (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)))=0 at he
          rw [he,map_zero]
        · intro i
          rw [← globalMixedSymVertex_intertwines q hq hq1 h p s c hs]
          have he:=(symmetricHighestRealization q hq hq1 (h+1) (p+c-s)).highestK i
          change typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
            (h+1) (p+c-s) _ (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)))=
              q^(mixedHighestDynkin (h+1) (p+c-s) 0 i) •
                quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)) at he
          rw [he,map_smul]⟩
  have hv : v≠0 := by
    intro he
    have hz:=congrArg Subtype.val he
    have hNorm:=globalMixedSymVertex_highest_norm q hq hq1 h p s c hs
    change v.val=0 at hz
    change LinearMap.BilinForm.tmul
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
      (occupationCompactBilin q (h+1) c) v.val v.val=1 at hNorm
    rw [hz,map_zero] at hNorm
    norm_num at hNorm
  apply finrank_one_of_line_embedding
    (physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) p s 0 c (globalTypeILeftCupIndex p s c 0 hs)) _
    (globalMixedSymHighestMap q hq hq1 h p s c) _
    (globalMixedSymHighestMap_mem_channel q hq hq1 h p s c hs) v hv
  · rw [← completeHighestLeftAction_eigenspace_eq_channel q hq hq1 (h+1) (by omega)
      p s 0 c (by omega) (Or.inl rfl)]
    exact completeHighestLeftAction_eigenspace_finrank q hq hq1 (h+1) (by omega)
      p s 0 c (by omega) (Or.inl rfl) (globalTypeILeftCupIndex p s c 0 hs)
  · intro v w he
    apply Subtype.ext
    apply globalMixedSymInclusion_injective q hq hq1 h p s c
    exact congrArg Subtype.val he


end AMSPhysical
#print axioms AMSPhysical.globalMixedSymHighestSpace_finrank_one

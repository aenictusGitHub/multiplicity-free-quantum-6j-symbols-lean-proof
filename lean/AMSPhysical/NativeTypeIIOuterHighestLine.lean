import NativeTypeIIInclusion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option Elab.async false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def nativeTypeIIOuterAction (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  typeATensorRepresentation q (ne_of_gt hq) (h+1)
    (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channelAction
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)

abbrev nativeTypeIIOuterHighestSpace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  typeAHighestSpace
    (V:=(typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channel ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (h+2)) c)
    q (h+1) (nativeTypeIIOuterAction q hq hq1 h a b c d r) (mixedHighestDynkin (h+1) d 0)

def nativeTypeIIOuterHighestMap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    nativeTypeIIOuterHighestSpace q hq hq1 h a b c d r →ₗ[ℝ]
      physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d where
  toFun v := ⟨nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r v.val,by
    obtain ⟨hE,hK⟩:=(mem_typeAHighestSpace q (h+1) _ _ v.val).mp v.property
    dsimp only [nativeTypeIIOuterAction] at hE hK
    apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
    constructor
    · intro i
      change typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a b c (typeAAlgebraGenerator q (h+1) i 0)
        (nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r v.val)=0
      rw [← nativeTypeIITwoRowInclusion_intertwines q hq hq1 (h+1) (by omega) a b c d r,hE,map_zero]
    · intro i
      change typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) a b c (typeAAlgebraGenerator q (h+1) i 2)
        (nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r v.val)=
          q^(mixedHighestDynkin (h+1) d 0 i) • nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r v.val
      rw [← nativeTypeIITwoRowInclusion_intertwines q hq hq1 (h+1) (by omega) a b c d r,hK,map_smul]⟩
  map_add' v w := by apply Subtype.ext;exact (nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r).map_add v.val w.val
  map_smul' b0 v := by apply Subtype.ext;exact (nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r).map_smul b0 v.val

theorem nativeTypeIIOuterHighestSpace_finrank_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    Module.finrank ℝ (nativeTypeIIOuterHighestSpace q hq hq1 h a b c d r)=1 := by
  let U : Type := (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channel ⊗[ℝ]
    quantumOccupationSpace ℝ (Fin (h+2)) c
  letI : AddCommGroup U := inferInstance
  letI : Module ℝ U := inferInstance
  let H : Submodule ℝ U := nativeTypeIIOuterHighestSpace q hq hq1 h a b c d r
  letI : AddCommGroup H := inferInstance
  letI : Module ℝ H := inferInstance
  let v : nativeTypeIIOuterHighestSpace q hq hq1 h a b c d r :=
    ⟨nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)),by
      apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
      constructor
      · intro i
        dsimp only [nativeTypeIIOuterAction]
        rw [← nativeTypeIIOuterVertex_intertwines q hq hq1 (h+1) (by omega) a b c d hbal r]
        have he:=(symmetricHighestRealization q hq hq1 (h+1) d).highestE i
        change typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          (h+1) d _ (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))=0 at he
        rw [he,map_zero]
      · intro i
        dsimp only [nativeTypeIIOuterAction]
        rw [← nativeTypeIIOuterVertex_intertwines q hq hq1 (h+1) (by omega) a b c d hbal r]
        have he:=(symmetricHighestRealization q hq hq1 (h+1) d).highestK i
        change typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          (h+1) d _ (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))=
            q^(mixedHighestDynkin (h+1) d 0 i) • quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d) at he
        rw [he,map_smul]⟩
  have hv : v≠0 := by
    intro he
    have hz:=congrArg Subtype.val he
    have hNorm:=nativeTypeIIOuterVertex_highest_norm q hq hq1 h a b c d hbal r
    change v.val=0 at hz
    change LinearMap.BilinForm.tmul (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channelPair
      (occupationOppositeBilin q (h+1) c) v.val v.val=1 at hNorm
    rw [hz,map_zero] at hNorm
    norm_num at hNorm
  apply finrank_one_of_line_embedding
    (physicalTypeIILeftHighestLine q hq hq1 (h+1) (by omega) a b c d r)
    (physicalTypeIILeftHighestLine_finrank q hq hq1 (h+1) (by omega) a b c d hbal r)
    (nativeTypeIIOuterHighestMap q hq hq1 h a b c d r) _ _ v hv
  · intro v w he
    apply Subtype.ext
    apply nativeTypeIITwoRowInclusion_injective q hq hq1 (h+1) (by omega) a b c d r
    exact congrArg Subtype.val he
  · intro v
    change nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r v.val∈
      physicalTypeIILeftChannel q hq hq1 (h+1) (by omega) a b c d r
    exact ⟨v.val,rfl⟩

end AMSPhysical
#print axioms AMSPhysical.nativeTypeIIOuterHighestSpace_finrank_one

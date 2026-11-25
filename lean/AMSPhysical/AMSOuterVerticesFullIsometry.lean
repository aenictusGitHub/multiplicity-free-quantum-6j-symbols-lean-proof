import SharedActualAMSVertexTable
import UnitIntertwinerFullIsometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem globalMixedSymVertex_full_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) (x y : quantumOccupationSpace ℝ (Fin (h+2)) (p+c-s)) :
    LinearMap.BilinForm.tmul (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
      (occupationCompactBilin q (h+1) c)
      (globalMixedSymVertex q hq hq1 h p s c hs x) (globalMixedSymVertex q hq hq1 h p s c hs y)=
      occupationCompactBilin q (h+1) (p+c-s) x y := by
  have hFull : (globalMixedSymInclusion q hq hq1 h p s c).comp
      (globalMixedSymVertex q hq hq1 h p s c hs)=globalTypeILeftFullTree q hq hq1 h p s c hs := by
    apply (symmetricHighestRealization q hq hq1 (h+1) (p+c-s)).full_intertwiner_unique
      (symmetricHighestRealization_channel_top q hq hq1 (h+1) (p+c-s))
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s c)
    · intro z v
      simp only [LinearMap.comp_apply]
      dsimp only [symmetricHighestRealization]
      rw [globalMixedSymVertex_intertwines q hq hq1 h p s c hs,
        globalMixedSymInclusion_intertwines q hq hq1 h p s c]
    · exact globalTypeILeftFullTree_intertwines q hq hq1 h p s c hs
    · exact (globalMixedSymVertex_inclusion_highest q hq hq1 h p s c hs).trans
        (globalTypeILeftFullTree_highest q hq hq1 h p s c hs).symm
  have hIso:=globalMixedSymInclusion_isometry q hq hq1 h p s c
    (globalMixedSymVertex q hq hq1 h p s c hs x) (globalMixedSymVertex q hq hq1 h p s c hs y)
  have hx:=DFunLike.congr_fun hFull x
  have hy:=DFunLike.congr_fun hFull y
  simp only [LinearMap.comp_apply] at hx hy
  have hTreeIso:=physicalTypeIUnitHighestTreeMap_isometry q hq hq1 (h+1) p s c (p+c-s)
    (globalTypeILeftVector q hq hq1 h p s c 0 hs)
    (physicalTypeILeftCoupling_unit q hq hq1 (h+1) (by omega) p s 0 c (by omega) (Or.inl rfl)
      (globalTypeILeftCupIndex p s c 0 hs)) x y
  exact hIso.symm.trans ((congrArg₂ (fun v w=>physicalTripleBilin q (h+1) p s c v w) hx hy).trans hTreeIso)

theorem globalSymMixedVertex_full_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (x y : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    LinearMap.BilinForm.tmul (occupationCompactBilin q (h+1) a)
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelPair
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs x)
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs y)=occupationCompactBilin q (h+1) d x y := by
  have hIso:=globalSymMixedInclusion_isometry q hq hq1 h a p s
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs x)
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs y)
  exact hIso.symm.trans (globalSharedTypeIRightTree_isometry q hq hq1 h a p s d hbal hs 0 x y)

theorem nativeTypeIIOuterVertex_full_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (x y : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    LinearMap.BilinForm.tmul (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channelPair
      (occupationOppositeBilin q (h+1) c)
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r x)
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r y)=
      occupationCompactBilin q (h+1) d x y := by
  let H:=physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r
  let hN:=physicalTypeIICalibratedLeft_unit q hq hq1 h a b c d hbal r
  let U:=physicalTypeIIUnitHighestTreeMap q hq hq1 (h+1) (by omega) a b c d H hN
  have hFull : (nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r).comp
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r)=U := by
    apply (symmetricHighestRealization q hq hq1 (h+1) d).full_intertwiner_unique
      (symmetricHighestRealization_channel_top q hq hq1 (h+1) d)
      (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c)
    · intro z v
      simp only [LinearMap.comp_apply]
      dsimp only [symmetricHighestRealization]
      rw [nativeTypeIIOuterVertex_intertwines q hq hq1 (h+1) (by omega) a b c d hbal r,
        nativeTypeIITwoRowInclusion_intertwines q hq hq1 (h+1) (by omega) a b c d r]
    · exact physicalTypeIIUnitHighestTreeMap_intertwines q hq hq1 (h+1) (by omega) a b c d H hN
    · exact (nativeTypeIIOuterVertex_calibrated_highest q hq hq1 h a b c d hbal r).trans
        (physicalTypeIIUnitHighestTreeMap_highest q hq hq1 (h+1) (by omega) a b c d H hN).symm
  have hIso:=nativeTypeIITwoRowInclusion_isometry q hq hq1 (h+1) (by omega) a b c d r
    (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r x)
    (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r y)
  have hx:=DFunLike.congr_fun hFull x
  have hy:=DFunLike.congr_fun hFull y
  simp only [LinearMap.comp_apply] at hx hy
  exact hIso.symm.trans ((congrArg₂ (fun v w=>physicalTypeIITripleBilin q (h+1) a b c v w) hx hy).trans
    (physicalTypeIIUnitHighestTreeMap_isometry q hq hq1 (h+1) (by omega) a b c d H hN x y))

end AMSPhysical
#print axioms AMSPhysical.globalMixedSymVertex_full_isometry
#print axioms AMSPhysical.globalSymMixedVertex_full_isometry
#print axioms AMSPhysical.nativeTypeIIOuterVertex_full_isometry

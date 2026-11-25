import QuantumCupRadialAction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupRankReduction_left (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    quantumCupRankReduction q hq n hn l m h c
        (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c v)=
      quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (by omega) l m (h+n-1) c
        (quantumCupRankReduction q hq n hn l m h c v) := by
  have he : ((h+n-1:ℕ):ℤ)=(h:ℤ)+(n:ℤ)-1 := by omega
  have hMaps : (quantumCupRankReduction q hq n hn l m h c).toLinearMap.comp
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)=
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (by omega) l m (h+n-1) c).comp
        (quantumCupRankReduction q hq n hn l m h c).toLinearMap := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumCupBasis_apply]
    rw [quantumCupLeftAction_vector,quantumCupRankReduction_vector]
    by_cases hs : quantumCupCanRaiseLeft l m c r
    · rw [dif_pos hs,map_add,map_smul,map_smul,quantumCupRankReduction_vector,quantumCupRankReduction_vector,
        map_smul,quantumCupLeftAction_vector,dif_pos hs]
      simp only [smul_add,smul_smul,he,quantumCupRaiseLeft]
      rw [quantumCupLeftDiagonal_rank_shift,quantumCupRankGauge_left_off q n hn]
      congr 1 <;> congr 1 <;> ring
    · rw [dif_neg hs,map_add,map_smul,map_zero,add_zero,quantumCupRankReduction_vector,
        map_smul,quantumCupLeftAction_vector,dif_neg hs,add_zero]
      simp only [smul_smul,he]
      rw [quantumCupLeftDiagonal_rank_shift]
      congr 1
      ring
  exact DFunLike.congr_fun hMaps v

theorem quantumCupRankReduction_right (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    quantumCupRankReduction q hq n hn l m h c
        (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c v)=
      quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (by omega) l m (h+n-1) c
        (quantumCupRankReduction q hq n hn l m h c v) := by
  have he : ((h+n-1:ℕ):ℤ)=(h:ℤ)+(n:ℤ)-1 := by omega
  have hMaps : (quantumCupRankReduction q hq n hn l m h c).toLinearMap.comp
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)=
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (by omega) l m (h+n-1) c).comp
        (quantumCupRankReduction q hq n hn l m h c).toLinearMap := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumCupBasis_apply]
    rw [quantumCupRightAction_vector,quantumCupRankReduction_vector]
    by_cases hs : quantumCupCanRaiseRight l m c r
    · rw [dif_pos hs,map_add,map_smul,map_smul,quantumCupRankReduction_vector,quantumCupRankReduction_vector,
        map_smul,quantumCupRightAction_vector,dif_pos hs]
      simp only [smul_add,smul_smul,he,quantumCupRaiseRight]
      have ht : r.val.val-1+1=r.val.val := by have h0:=hs.1;omega
      have hOff:=quantumCupRankGauge_right_off q n hn (l:ℤ) (h:ℤ) (c:ℤ) (r.val.val-1) (m-r.val.val)
      rw [ht] at hOff
      rw [quantumCupLeftDiagonal_rank_shift,hOff]
      congr 1 <;> congr 1 <;> ring
    · rw [dif_neg hs,map_add,map_smul,map_zero,add_zero,quantumCupRankReduction_vector,
        map_smul,quantumCupRightAction_vector,dif_neg hs,add_zero]
      simp only [smul_smul,he]
      rw [quantumCupLeftDiagonal_rank_shift]
      congr 1
      ring
  exact DFunLike.congr_fun hMaps v

end AMSPhysical
#print axioms AMSPhysical.quantumCupRankReduction_left
#print axioms AMSPhysical.quantumCupRankReduction_right

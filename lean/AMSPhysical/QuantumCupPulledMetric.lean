import QuantumCupPhysicalAdjoint
import BilinearFormAdjoints

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupRankPulledBilin (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    quantumCupSpan q n l m h c →ₗ[ℝ] quantumCupSpan q n l m h c →ₗ[ℝ] ℝ :=
  ((quantumCupPhysicalBilin q 1 l m (h+n-1) c).comp
    (quantumCupRankReduction q hq n hn l m h c).toLinearMap).compl₂
      (quantumCupRankReduction q hq n hn l m h c).toLinearMap

theorem quantumCupRankPulledBilin_leftAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) : PairAdjoint (V:=quantumCupSpan q n l m h c) (quantumCupRankPulledBilin q hq n hn l m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c) := by
  let V := quantumCupSpan q n l m h c
  let W := quantumCupSpan q 1 l m (h+n-1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact pairAdjoint_pullback_intertwiner (V:=V) (W:=W) _ _ _ _
    (quantumCupLeftAction_physical_selfAdjoint q hq hq1 1 (by omega) l m (h+n-1) c)
    (quantumCupRankReduction_left q hq hq1 n hn l m h c)

theorem quantumCupRankPulledBilin_rightAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) : PairAdjoint (V:=quantumCupSpan q n l m h c) (quantumCupRankPulledBilin q hq n hn l m h c)
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c) := by
  let V := quantumCupSpan q n l m h c
  let W := quantumCupSpan q 1 l m (h+n-1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact pairAdjoint_pullback_intertwiner (V:=V) (W:=W) _ _ _ _
    (quantumCupRightAction_physical_selfAdjoint q hq hq1 1 (by omega) l m (h+n-1) c)
    (quantumCupRankReduction_right q hq hq1 n hn l m h c)

theorem quantumCupRankPulledBilin_pos (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (v : quantumCupSpan q n l m h c) (hv : v≠0) : 0<quantumCupRankPulledBilin q hq n hn l m h c v v := by
  apply quantumCupPhysicalBilin_pos q hq 1 (by omega)
  intro he
  change quantumCupRankReduction q hq n hn l m h c v=0 at he
  apply hv
  apply (quantumCupRankReduction q hq n hn l m h c).injective
  rw [he,map_zero]

end AMSPhysical

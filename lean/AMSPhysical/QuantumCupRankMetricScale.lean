import QuantumCupPulledMetric
import QuantumCupGramUnique

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupRankMetricScale (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m ≤ l+c) : ℝ :=
  let v := quantumCupBasis q hq n hn l m h c (quantumCupTop l m c hadm)
  quantumCupRankPulledBilin q hq n hn l m h c v v/quantumCupPhysicalBilin q n l m h c v v

theorem quantumCupRankMetricScale_pos (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) : 0<quantumCupRankMetricScale q hq n hn l m h c hadm := by
  unfold quantumCupRankMetricScale
  apply div_pos
  · exact quantumCupRankPulledBilin_pos q hq n hn l m h c _ ((quantumCupBasis q hq n hn l m h c).ne_zero _)
  · exact quantumCupPhysicalBilin_pos q hq n hn l m h c _ ((quantumCupBasis q hq n hn l m h c).ne_zero _)

/-- The independently constructed simultaneous rank-reduction map preserves
the actual physical metric up to a SINGLE proved positive scalar. -/
theorem quantumCupRankReduction_metric (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) (v w : quantumCupSpan q n l m h c) :
    quantumCupPhysicalBilin q 1 l m (h+n-1) c
        (quantumCupRankReduction q hq n hn l m h c v) (quantumCupRankReduction q hq n hn l m h c w)=
      quantumCupRankMetricScale q hq n hn l m h c hadm*quantumCupPhysicalBilin q n l m h c v w := by
  let V := quantumCupSpan q n l m h c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let B := quantumCupPhysicalBilin q n l m h c
  let C := quantumCupRankPulledBilin q hq n hn l m h c
  let scaleValue := quantumCupRankMetricScale q hq n hn l m h c hadm
  let A := quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c
  let D := quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c
  have hHA : PairAdjoint (V:=V) (C-scaleValue • B) A A :=
    pairAdjoint_form_sub (V:=V) C (scaleValue • B) A (quantumCupRankPulledBilin_leftAdjoint q hq hq1 n hn l m h c)
      (pairAdjoint_form_smul (V:=V) B A (quantumCupLeftAction_physical_selfAdjoint q hq hq1 n hn l m h c) scaleValue)
  have hHD : PairAdjoint (V:=V) (C-scaleValue • B) D D :=
    pairAdjoint_form_sub (V:=V) C (scaleValue • B) D (quantumCupRankPulledBilin_rightAdjoint q hq hq1 n hn l m h c)
      (pairAdjoint_form_smul (V:=V) B D (quantumCupRightAction_physical_selfAdjoint q hq hq1 n hn l m h c) scaleValue)
  let topv := quantumCupBasis q hq n hn l m h c (quantumCupTop l m c hadm)
  have hNorm : (C-scaleValue • B) topv topv=0 := by
    change C topv topv-(C topv topv/B topv topv)*B topv topv=0
    rw [div_mul_cancel₀ _ (ne_of_gt (quantumCupPhysicalBilin_pos q hq n hn l m h c _
      ((quantumCupBasis q hq n hn l m h c).ne_zero _))),sub_self]
  have hH:=quantumCupRadial_form_zero q hq hq1 n hn l m h c hadm (C-scaleValue • B) hHA hHD hNorm
  have hForms : C=scaleValue • B := sub_eq_zero.mp hH
  exact DFunLike.congr_fun (DFunLike.congr_fun hForms v) w

end AMSPhysical
#print axioms AMSPhysical.quantumCupRankReduction_metric

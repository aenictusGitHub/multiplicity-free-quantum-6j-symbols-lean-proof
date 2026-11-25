import QuantumCupRankMetricScale

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupRankNormalization (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m ≤ l+c) : ℝ :=
  (Real.sqrt (quantumCupRankMetricScale q hq n hn l m h c hadm))⁻¹

theorem quantumCupRankNormalization_pos (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m ≤ l+c) :
    0<quantumCupRankNormalization q hq n hn l m h c hadm :=
  inv_pos.mpr (Real.sqrt_pos.mpr (quantumCupRankMetricScale_pos q hq n hn l m h c hadm))

theorem quantumCupRankNormalization_scale (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m ≤ l+c) :
    quantumCupRankNormalization q hq n hn l m h c hadm*quantumCupRankNormalization q hq n hn l m h c hadm*
      quantumCupRankMetricScale q hq n hn l m h c hadm=1 := by
  let scaleValue := quantumCupRankMetricScale q hq n hn l m h c hadm
  have hscaleValue : 0<scaleValue := quantumCupRankMetricScale_pos q hq n hn l m h c hadm
  have hs : Real.sqrt scaleValue≠0 := ne_of_gt (Real.sqrt_pos.mpr hscaleValue)
  change (Real.sqrt scaleValue)⁻¹*(Real.sqrt scaleValue)⁻¹*scaleValue=1
  calc
    _ = (Real.sqrt scaleValue)⁻¹*(Real.sqrt scaleValue)⁻¹*(Real.sqrt scaleValue)^2 := by rw [Real.sq_sqrt hscaleValue.le]
    _ = _ := by field_simp

/-- The derived positive scalar correction makes the explicit simultaneous
cup rank reduction an actual physical-metric isometry. -/
def quantumCupUnitaryRankReduction (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) :
    quantumCupSpan q n l m h c ≃ₗ[ℝ] quantumCupSpan q 1 l m (h+n-1) c :=
  (quantumCupRankReduction q hq n hn l m h c).trans
    (LinearEquiv.smulOfNeZero ℝ (quantumCupSpan q 1 l m (h+n-1) c)
      (quantumCupRankNormalization q hq n hn l m h c hadm)
      (ne_of_gt (quantumCupRankNormalization_pos q hq n hn l m h c hadm)))

theorem quantumCupUnitaryRankReduction_apply (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) (v : quantumCupSpan q n l m h c) :
    quantumCupUnitaryRankReduction q hq n hn l m h c hadm v=
      quantumCupRankNormalization q hq n hn l m h c hadm • quantumCupRankReduction q hq n hn l m h c v := rfl

theorem quantumCupUnitaryRankReduction_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) (v w : quantumCupSpan q n l m h c) :
    quantumCupPhysicalBilin q 1 l m (h+n-1) c
      (quantumCupUnitaryRankReduction q hq n hn l m h c hadm v)
      (quantumCupUnitaryRankReduction q hq n hn l m h c hadm w)=quantumCupPhysicalBilin q n l m h c v w := by
  rw [quantumCupUnitaryRankReduction_apply,quantumCupUnitaryRankReduction_apply]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [quantumCupRankReduction_metric q hq hq1 n hn l m h c hadm]
  calc
    _ = (quantumCupRankNormalization q hq n hn l m h c hadm*quantumCupRankNormalization q hq n hn l m h c hadm*
      quantumCupRankMetricScale q hq n hn l m h c hadm)*quantumCupPhysicalBilin q n l m h c v w := by ring
    _ = _ := by rw [quantumCupRankNormalization_scale,one_mul]

theorem quantumCupUnitaryRankReduction_left (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) (v : quantumCupSpan q n l m h c) :
    quantumCupUnitaryRankReduction q hq n hn l m h c hadm
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c v)=
      quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (by omega) l m (h+n-1) c
        (quantumCupUnitaryRankReduction q hq n hn l m h c hadm v) := by
  rw [quantumCupUnitaryRankReduction_apply,quantumCupUnitaryRankReduction_apply,quantumCupRankReduction_left q hq hq1,map_smul]

theorem quantumCupUnitaryRankReduction_right (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) (v : quantumCupSpan q n l m h c) :
    quantumCupUnitaryRankReduction q hq n hn l m h c hadm
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c v)=
      quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 (by omega) l m (h+n-1) c
        (quantumCupUnitaryRankReduction q hq n hn l m h c hadm v) := by
  rw [quantumCupUnitaryRankReduction_apply,quantumCupUnitaryRankReduction_apply,quantumCupRankReduction_right q hq hq1,map_smul]

end AMSPhysical
#print axioms AMSPhysical.quantumCupUnitaryRankReduction_isometry

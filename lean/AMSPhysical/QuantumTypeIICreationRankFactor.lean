import QuantumTypeIICreationDimensionRatio

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical

/-- Literal unit-basis matrix of actual physical Type-II cup creation. -/
def physicalTypeIICreationMatrix (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (a b c d:ℕ) (hbal:a+b=c+d) :
    Matrix (TypeIICommonIndex a (b+1) (c+1) d) (TypeIICommonIndex a b c d) ℝ := fun s r=>
  (physicalTypeIILeftBasis q hq hq1 n hn a (b+1) (c+1) d (by omega)).repr
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d
      (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r)) s

def typeIICreationDimensionFactor (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (a b c d:ℕ) (r:TypeIICommonIndex a b c d) (s:TypeIICommonIndex a (b+1) (c+1) d) :ℝ :=
  Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 n hn ((a-s.val)+(b+1-s.val)) s.val/
    twoRowIrrepQuantumDimension q hq hq1 n hn ((a-r.val)+(b-r.val)) r.val)

theorem typeIICreationDimensionFactor_pos (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (a b c d:ℕ) (r:TypeIICommonIndex a b c d) (s:TypeIICommonIndex a (b+1) (c+1) d) :
    0<typeIICreationDimensionFactor q hq hq1 n hn a b c d r s :=
  Real.sqrt_pos.mpr (div_pos (twoRowIrrepQuantumDimension_pos q hq hq1 n hn _ _)
    (twoRowIrrepQuantumDimension_pos q hq hq1 n hn _ _))

/-- Entire arbitrary-rank ACTUAL unit creation matrix reduced to its actual
rank-two unit matrix, with a completely proved positive Weyl-dimension factor.
The AMS shifted-label spectral identification remains a separate obligation. -/
theorem physicalTypeIICreationMatrix_rank_factor (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (s:TypeIICommonIndex a (b+1) (c+1) d) :
    physicalTypeIICreationMatrix q hq hq1 n hn a b c d hbal s r=
      (typeIICreationDimensionFactor q hq hq1 n hn a b c d r s/
        typeIICreationDimensionFactor q hq hq1 1 (by omega) a b c d r s)*
      physicalTypeIICreationMatrix q hq hq1 1 (by omega) a b c d hbal s r := by
  have hk:typeIICreationDimensionFactor q hq hq1 1 (by omega) a b c d r s≠0:=
    ne_of_gt (typeIICreationDimensionFactor_pos q hq hq1 1 (by omega) a b c d r s)
  unfold physicalTypeIICreationMatrix
  rw [physicalTypeIIHighestRightCreation_dimension_ratio q hq hq1 n hn a b c d hbal r s,
    physicalTypeIIHighestRightCreation_dimension_ratio q hq hq1 1 (by omega) a b c d hbal r s]
  change _=(_/typeIICreationDimensionFactor q hq hq1 1 (by omega) a b c d r s)*
    (typeIICreationDimensionFactor q hq hq1 1 (by omega) a b c d r s*_)
  rw [← mul_assoc,div_mul_cancel₀ _ hk]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIICreationMatrix_rank_factor

import ActualAMSQuadrilateralComparison
import PhysicalTripleIntrinsicMetrics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem physicalTripleBilin_eq_intrinsic_all (q : ℝ) (n a s p : ℕ) :
    physicalTripleBilin q n a s p = LinearMap.BilinForm.tmul
      (occupationCompactBilin q n a) (LinearMap.BilinForm.tmul
        (occupationOppositeBilin q n s) (occupationCompactBilin q n p)) := by
  rw [physicalTripleBilin_eq_intrinsic_right,reverseMixedTensorBilin_eq_intrinsic]

theorem physicalTypeIITripleBilin_eq_intrinsic_all (q : ℝ) (n a b c : ℕ) :
    physicalTypeIITripleBilin q n a b c = LinearMap.BilinForm.tmul
      (occupationCompactBilin q n a) (LinearMap.BilinForm.tmul
        (occupationCompactBilin q n b) (occupationOppositeBilin q n c)) := by
  unfold physicalTypeIITripleBilin
  rw [tensorWeightedBilin_eq_intrinsic]
  change LinearMap.BilinForm.tmul (occupationCompactBilin q n a) (mixedTensorBilin q n b c)=_
  rw [mixedTensorBilin_eq_intrinsic]

/-- Actual recoupling: compose the one shared trivalent table along the
left and right trees, and take their intrinsic tensor-product pairing. -/
def actualTypeIRecouplingMatrix (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (l m c : ℕ) : Matrix (QuantumCupIndex l m c) (QuantumCupIndex l m c) ℝ :=
  fun s t => actualTriplePair
    (actualSymmetricCarrier q hq hq1 (h+1) l).irrep
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) m).irrep
    (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
    (actualTypeILeftHighest q hq hq1 h hh l m c s)
    (actualTypeIRightHighest q hq hq1 h hh l m c t)

def actualTypeIIRecouplingMatrix (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (a b c d : ℕ) : Matrix (TypeIICommonIndex a b c d) (QuantumCupIndex a c b) ℝ :=
  fun r t => actualTriplePair
    (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
    (actualSymmetricCarrier q hq hq1 (h+1) b).irrep
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep
    (actualTypeIILeftHighest q hq hq1 h hh a b c d r)
    (actualTypeIIRightHighest q hq hq1 h hh a b c d t)

theorem actualTypeIRecouplingMatrix_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    actualTypeIRecouplingMatrix q hq hq1 h hh l m c s t =
      physicalTripleBilin q (h+1) l m c
        (physicalTypeILeftCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) s).val
        (physicalTypeIRightCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) t).val := by
  unfold actualTypeIRecouplingMatrix
  rw [actualTypeILeftHighest_calibrated q hq hq1 h hh l m c hadm,
    actualTypeIRightHighest_calibrated q hq hq1 h hh l m c hadm]
  unfold actualTriplePair
  rw [canonicalizeActualTriple_isometry]
  rw [physicalTripleBilin_eq_intrinsic_all]
  rfl

theorem actualTypeIIRecouplingMatrix_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    actualTypeIIRecouplingMatrix q hq hq1 h hh a b c d r t =
      physicalTypeIITripleBilin q (h+1) a b c
        (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val
        (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val := by
  unfold actualTypeIIRecouplingMatrix
  rw [actualTypeIILeftHighest_calibrated q hq hq1 h hh a b c d hbal,
    actualTypeIIRightHighest_calibrated q hq hq1 h hh a b c d hbal,
    amsSharedNative_common_phase_cancels]
  unfold actualTriplePair
  rw [canonicalizeActualTriple_isometry]
  rw [physicalTypeIITripleBilin_eq_intrinsic_all]
  rfl

end AMSPhysical
#print axioms AMSPhysical.actualTypeIRecouplingMatrix_calibrated
#print axioms AMSPhysical.actualTypeIIRecouplingMatrix_calibrated

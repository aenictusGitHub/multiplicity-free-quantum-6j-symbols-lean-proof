import TypeIIShiftedBentFamily
import TriangularSpanCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIShiftedSelectedCoordinateNat (h a b c d y:ℕ):
    (finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) →ₗ[ℝ] ℝ:=
  if hy:y<min (min a b) (min c d)+1 then typeIIShiftedSelectedCoordinate h a b c d ⟨y,hy⟩ else 0

theorem typeIIShiftedSelectedCoordinateNat_below (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (y:ℕ) (hy:y<r.val):
    typeIIShiftedSelectedCoordinateNat h a b c d y (typeIIShiftedBentHighest q hq hq1 h a b c d hbal r)=0 := by
  rw [typeIIShiftedSelectedCoordinateNat,dif_pos (lt_trans hy r.isLt)]
  exact typeIIShiftedSelectedCoordinate_below q hq hq1 h a b c d hbal r ⟨y,lt_trans hy r.isLt⟩ hy

theorem typeIIShiftedSelectedCoordinateNat_diagonal (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedSelectedCoordinateNat h a b c d r.val (typeIIShiftedBentHighest q hq hq1 h a b c d hbal r)≠0 := by
  rw [typeIIShiftedSelectedCoordinateNat,dif_pos r.isLt]
  change typeIIShiftedSelectedCoordinate h a b c d r (typeIIShiftedBentHighest q hq hq1 h a b c d hbal r)≠0
  rw [typeIIShiftedSelectedCoordinate_leading]
  exact typeIIShiftedLeadingCoefficient_ne_zero q hq h a b c d r

theorem typeIIShiftedBentHighest_linearIndependent (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):
    LinearIndependent ℝ (typeIIShiftedBentHighest q hq hq1 h a b c d hbal) := by
  let V:=finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
    (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact triangularFamily_linearIndependent (V:=V) _ Fin.val Fin.val_injective (typeIIShiftedSelectedCoordinateNat h a b c d)
    (typeIIShiftedSelectedCoordinateNat_below q hq hq1 h a b c d hbal)
    (typeIIShiftedSelectedCoordinateNat_diagonal q hq hq1 h a b c d hbal)

def typeIIShiftedBentSpan (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ) (hbal:a+b=c+d):
    Submodule ℝ (finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :=
  Submodule.span ℝ (Set.range (typeIIShiftedBentHighest q hq hq1 h a b c d hbal))

/-- Selected coordinates determine every vector in the entire independently
constructed shifted bent span. No metric identification is assumed. -/
theorem typeIIShiftedBentSpan_coordinate_ext (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v w:finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c))
    (hv:v∈typeIIShiftedBentSpan q hq hq1 h a b c d hbal)
    (hw:w∈typeIIShiftedBentSpan q hq hq1 h a b c d hbal)
    (hc:∀ k:TypeIICommonIndex a b c d,typeIIShiftedSelectedCoordinate h a b c d k v=
      typeIIShiftedSelectedCoordinate h a b c d k w):v=w := by
  let V:=finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
    (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply triangular_span_ext (V:=V) (typeIIShiftedBentHighest q hq hq1 h a b c d hbal) Fin.val Fin.val_injective
    (typeIIShiftedSelectedCoordinateNat h a b c d)
    (typeIIShiftedSelectedCoordinateNat_below q hq hq1 h a b c d hbal)
    (typeIIShiftedSelectedCoordinateNat_diagonal q hq hq1 h a b c d hbal) v w hv hw
  intro y
  unfold typeIIShiftedSelectedCoordinateNat
  split_ifs with hy
  · exact hc ⟨y,hy⟩
  · rfl

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedBentHighest_linearIndependent
#print axioms AMSPhysical.typeIIShiftedBentSpan_coordinate_ext

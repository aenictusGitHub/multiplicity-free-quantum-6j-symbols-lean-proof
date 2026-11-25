import TwoRowHighestBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

abbrev TwoRowFusionIndex (l m : ℕ) := Fin (min l m+1)

def twoRowHighestAt (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  twoRowHighest q n hn l m r.val (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)

def twoRowBoundaryAt (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    occupationWeights (Fin (n+1)) m := twoVertexOccupation n hn m ⟨r.val,by have h:=r.isLt;omega⟩

theorem twoRowBoundaryAt_injective (n : ℕ) (hn : 0<n) (l m : ℕ) :
    Function.Injective (twoRowBoundaryAt n hn l m) := by
  intro r s h
  have he:=twoVertexOccupation_injective n hn m h
  apply Fin.ext
  exact congrArg (fun z : Fin (m+1) => z.val) he

theorem twoRowHighestAt_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) (i : Fin n) :
    typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) (twoRowHighestAt q n hn l m r)=0 :=
  twoRowHighest_E_zero q hq hq1 n hn l m r.val _ _ i

theorem twoRowHighestAt_boundary (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (twoRowHighestAt q n hn l m r)
      ((highestOccupation n l).val,y.val)=(if twoRowBoundaryAt n hn l m r=y then 1 else 0) :=
  twoRowHighest_boundary_coefficient q n hn l m r.val _ _ y

end AMSPhysical

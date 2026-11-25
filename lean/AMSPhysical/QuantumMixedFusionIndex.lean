import QuantumMixedFusionBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

abbrev MixedFusionIndex (l m : ℕ) := Fin (min l m+1)

def mixedFusionHighestAt (q : ℝ) (n l m : ℕ) (r : MixedFusionIndex l m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  mixedFusionHighest q n l m r.val (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)

def mixedBoundaryAt (n l m : ℕ) (r : MixedFusionIndex l m) : occupationWeights (Fin (n+1)) m :=
  mixedBoundaryOccupation n m r.val (by have h:=r.isLt;omega)

theorem mixedBoundaryAt_injective (n l m : ℕ) (hn : 0<n) : Function.Injective (mixedBoundaryAt n l m) := by
  intro r s h
  apply Fin.ext
  exact mixedBoundaryOccupation_injective n m hn r.val s.val _ _ h

theorem mixedFusionHighestAt_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (r : MixedFusionIndex l m) (i : Fin n) :
    typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) (mixedFusionHighestAt q n l m r)=0 :=
  mixedFusionHighest_E_zero q hq hq1 n l m r.val _ _ i

theorem mixedFusionHighestAt_boundary (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : MixedFusionIndex l m) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (mixedFusionHighestAt q n l m r)
      ((highestOccupation n l).val,y.val)=(if mixedBoundaryAt n l m r=y then 1 else 0) :=
  mixedFusionHighest_boundary_coefficient q hq n hn l m r.val _ _ y

end AMSPhysical

import QuantumTypeIIRightCreation
import QuantumTypeIIBoundaryEquivalence
import TwoVertexCreationFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIStandardRightCreation (q : ℝ) (a b c : ℕ) :
    (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) (b+1) ⊗[ℝ] finiteWeightSpace (K:=ℝ) (c+1))) :=
  TensorProduct.map LinearMap.id (mixedTwoVertexCompressedCreation q 1 (by omega) b c)

/-- Literal restriction intertwines the actual physical Type-II cup map
with its independently computed rank-independent two-term formula. -/
theorem physicalTypeIIRightCreation_boundary (q : ℝ) (n : ℕ) (hn : 0<n) (a b c : ℕ)
    (v : quantumOccupationTripleSpace n a b c) :
    twoVertexTripleProjection n hn a (b+1) (c+1) (physicalTypeIIRightCreation q n a b c v)=
      typeIIStandardRightCreation q a b c (twoVertexTripleProjection n hn a b c v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul u v =>
    simp only [physicalTypeIIRightCreation,twoVertexTripleProjection,typeIIStandardRightCreation,
      TensorProduct.map_tmul,LinearMap.id_apply]
    rw [mixedFiniteCreation_boundary_compression,mixedTwoVertexCompressedCreation_rank_independent]

/-- Complete same-label linear boundary transport intertwines actual cup
creation in every rank. This is NOT an isometry or AMS shifted-label claim. -/
theorem physicalTypeIIUnshiftedBoundaryEquiv_right_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal:a+b=c+d)
    (v:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :
    physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a (b+1) (c+1) d (by omega)
      (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d v)=
      physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
        (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal v) := by
  apply physicalTypeIIHighestBoundaryMap_injective q hq hq1 1 (by omega) a (b+1) (c+1) d (by omega)
  rw [← physicalTypeIIUnshiftedBoundaryEquiv_coordinates]
  change twoVertexTripleProjection n hn a (b+1) (c+1)
      (physicalTypeIIRightCreation q n a b c v.val)=
    twoVertexTripleProjection 1 (by omega) a (b+1) (c+1)
      (physicalTypeIIRightCreation q 1 a b c
        (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal v).val)
  rw [physicalTypeIIRightCreation_boundary,physicalTypeIIRightCreation_boundary]
  congr 1
  exact physicalTypeIIUnshiftedBoundaryEquiv_coordinates q hq hq1 n hn a b c d hbal v

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIUnshiftedBoundaryEquiv_right_creation

import QuantumTypeIIHighestBoundary
import QuantumTypeIILeftRawBasis
import TwoVertexRankTwoProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 350000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIStandardLeftHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :=
  typeIIStandardLeftTreeMap q hq hq1 a b c d hbal r (standardWeightBasis (K:=ℝ) d 0)

theorem typeIIStandardLeftHighest_linearIndependent (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    LinearIndependent ℝ (typeIIStandardLeftHighest q hq hq1 a b c d hbal) := by
  let H:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
  let W:=finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)
  letI : AddCommGroup H := inferInstance
  letI : Module ℝ H := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  let f : H →ₗ[ℝ] W :=
    (twoVertexTripleProjection 1 (by omega) a b c).comp H.subtype
  have hf : Function.Injective f:=(twoVertexTripleProjection_rankTwo_injective a b c).comp Subtype.val_injective
  have hi : LinearIndependent ℝ (f ∘ (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal)) :=
    (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal).linearIndependent.map' (M:=H) (M':=W) f (LinearMap.ker_eq_bot.mpr hf)
  change LinearIndependent ℝ (fun r =>twoVertexTripleProjection 1 (by omega) a b c
    ((physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal r).val)) at hi
  simpa only [physicalTypeIILeftRawBasis_apply,physicalTypeIILeftHighest_boundary,typeIIStandardLeftHighest] using hi

def physicalTypeIIHighestBoundaryMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :=
  (twoVertexTripleProjection n hn a b c).comp
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d).subtype

/-- Literal boundary restriction is injective on the ENTIRE independently
defined physical Type-II highest space, in every rank and admissible degree. -/
theorem physicalTypeIIHighestBoundaryMap_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) :
    Function.Injective (physicalTypeIIHighestBoundaryMap q hq hq1 n hn a b c d) := by
  refine LinearMap.injective_of_linearIndependent (R:=ℝ)
    (M:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (N:=finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c))
    (f:=physicalTypeIIHighestBoundaryMap q hq hq1 n hn a b c d)
    (v:=physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal)
    (physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal).span_eq ?_
  simpa only [physicalTypeIIHighestBoundaryMap,Function.comp_def,LinearMap.comp_apply,
    Submodule.subtype_apply,physicalTypeIILeftRawBasis_apply,physicalTypeIILeftHighest_boundary,typeIIStandardLeftHighest] using
      typeIIStandardLeftHighest_linearIndependent q hq hq1 a b c d hbal

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIHighestBoundaryMap_injective

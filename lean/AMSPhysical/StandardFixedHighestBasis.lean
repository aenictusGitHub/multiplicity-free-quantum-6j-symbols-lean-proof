import StandardCupHighestVectors
import QuantumFixedHighest
import QuantumTypeIILeftBasis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

/-- The actual standard unit left coupling at fixed total highest weight. -/
def standardFixedLeftHighest (q:ℝ) (hq:0<q) (hq1:q≠1) (l m c H:ℕ)
    (p:FixedLeftHighest l m c H):
    standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H := by
  refine ⟨quantumLeftTreeHighest q hq hq1 l m c p.val.1 p.val.2,?_⟩
  apply (standardTypeAHighest_mem_iff q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H _).mpr
  refine ⟨quantumLeftTreeHighest_E q hq hq1 l m c p.val,?_⟩
  have he:=quantumLeftTreeHighest_K q hq hq1 l m c p.val
  change _=q^(leftTotalLabel l m c p.val:ℤ) • _ at he
  rwa [p.property] at he

theorem standardFixedLeftHighest_pair (q:ℝ) (hq:0<q) (hq1:q≠1) (l m c H:ℕ)
    (p v:FixedLeftHighest l m c H):
    quantumTripleBilin q l m c (standardFixedLeftHighest q hq hq1 l m c H p).val
      (standardFixedLeftHighest q hq hq1 l m c H v).val=if p=v then 1 else 0 := by
  classical
  have hi:Function.Injective (fun p:FixedLeftHighest l m c H=>leftHighestEmbedding l m c p.val):=
    (leftHighestEmbedding_injective l m c).comp Subtype.val_injective
  simpa only [leftFusionHighest_eq,hi.eq_iff] using
    leftFusionVector_pair q hq hq1 l m c (leftHighestEmbedding l m c p.val) (leftHighestEmbedding l m c v.val)

theorem standardFixedLeftHighest_expansion (q:ℝ) (hq:0<q) (hq1:q≠1) (l m c H:ℕ)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H):
    (∑ p:FixedLeftHighest l m c H, quantumTripleBilin q l m c v.val
      (standardFixedLeftHighest q hq hq1 l m c H p).val •
        standardFixedLeftHighest q hq hq1 l m c H p)=v := by
  apply Subtype.ext
  have hv:=(standardTypeAHighest_mem_iff q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H v.val).mp v.property
  simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower] using
    quantumHighest_fixed_left_expansion q hq hq1 l m c H v.val hv.1 hv.2

def standardFixedLeftHighestBasis (q:ℝ) (hq:0<q) (hq1:q≠1) (l m c H:ℕ):
    Module.Basis (FixedLeftHighest l m c H) ℝ
      (standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H) := by
  let V:=standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  have hi:LinearIndependent ℝ (standardFixedLeftHighest q hq hq1 l m c H):=
    bilinear_orthonormal_independent (V:=V)
      (restrictedBilinearPair (quantumTripleBilin q l m c) V)
      (standardFixedLeftHighest q hq hq1 l m c H) (standardFixedLeftHighest_pair q hq hq1 l m c H)
  refine Module.Basis.mk hi ?_
  intro v hv
  rw [← standardFixedLeftHighest_expansion q hq hq1 l m c H v]
  exact Submodule.sum_mem _ (fun p _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨p,rfl⟩))

theorem standardFixedLeftHighestBasis_apply (q:ℝ) (hq:0<q) (hq1:q≠1) (l m c H:ℕ)
    (p:FixedLeftHighest l m c H):
    standardFixedLeftHighestBasis q hq hq1 l m c H p=standardFixedLeftHighest q hq hq1 l m c H p := by
  rw [standardFixedLeftHighestBasis,Module.Basis.mk_apply]

end AMSPhysical
#print axioms AMSPhysical.standardFixedLeftHighestBasis

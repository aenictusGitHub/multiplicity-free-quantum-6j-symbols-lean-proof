import GlobalCupHighestFirstBoundary
import RankTwoTypeIFirstBoundary
import PhysicalTypeICouplingVectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def physicalHighestFirstBoundary (n l m h c : ℕ) : quantumOccupationTripleSpace n l (m+h) c →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (quantumCupBoundaryPoint n (l:ℤ) (h:ℤ) (c:ℤ) 0 m)).comp
    (occupationTripleCoefficients n l (m+h) c)

theorem rankTwoMixedTripleEquiv_highest_first_boundary (l m h c : ℕ) (hm : m≤c)
    (v : RealQuantumTripleSpace l (m+h) c) :
    physicalHighestFirstBoundary 1 l m h c (rankTwoMixedTripleEquiv l (m+h) c v) =
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+h))).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr v ((0,0),⟨m,by omega⟩) := by
  have he : occupationTripleEmbedding 1 l (m+h) c
      (rankTwoMixedTripleIndex l (m+h) c ((0,0),⟨m,by omega⟩)) =
      quantumCupBoundaryPoint 1 (l:ℤ) (h:ℤ) (c:ℤ) 0 m := by
    apply Prod.ext
    · change (twoVertexOccupation 1 (by omega) l 0).val = _
      rw [twoVertexOccupation_zero]
      rfl
    · apply Prod.ext
      · funext j
        fin_cases j <;>
          simp [occupationTripleEmbedding,rankTwoMixedTripleIndex,twoVertexOccupation,
            quantumCupBoundaryPoint,secondVertex,Fin.val_rev,Pi.single_apply] <;> omega
      · funext j
        fin_cases j <;>
          simp [occupationTripleEmbedding,rankTwoMixedTripleIndex,twoVertexOccupation,
            quantumCupBoundaryPoint,secondVertex,Pi.single_apply] <;> omega
  change occupationTripleCoefficients 1 l (m+h) c (rankTwoMixedTripleEquiv l (m+h) c v) _ = _
  rw [← he]
  exact rankTwoMixedTripleEquiv_coefficient l (m+h) c v ((0,0),⟨m,by omega⟩)

theorem physicalCupUnitaryRankReduction_highest_first_boundary (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hm : m≤c) (hadm : m≤l+c)
    (v : physicalQuantumCupSpan q n l m h c) :
    physicalHighestFirstBoundary 1 l m (h+n-1) c
      (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm v).val =
      (quantumCupRankNormalization q hq n hn l m h c hadm * q^(-((n-1:ℕ):ℤ)*(m:ℤ))) *
        physicalHighestFirstBoundary n l m h c v.val := by
  have he:=physicalQuantumCupCoefficientEquiv_literal q hq 1 (by omega) l m (h+n-1) c
    (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm v)
  unfold physicalQuantumCupUnitaryRankReduction at he
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] at he
  change (quantumCupUnitaryRankReduction q hq n hn l m h c hadm
    (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v)).val =
      occupationTripleCoefficients 1 l (m+(h+n-1)) c
        (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm v).val at he
  change occupationTripleCoefficients 1 l (m+(h+n-1)) c
    (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm v).val _ = _
  rw [← he]
  change cupHighestFirstBoundaryEval q 1 l m (h+n-1) c
    (quantumCupUnitaryRankReduction q hq n hn l m h c hadm
      (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v)) = _
  rw [quantumCupUnitaryRankReduction_apply,map_smul,smul_eq_mul,
    quantumCupRankReduction_highest_first_boundary q hq n hn l m h c hm]
  change _ * (_ * (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v).val _) = _
  rw [physicalQuantumCupCoefficientEquiv_literal]
  simp only [physicalHighestFirstBoundary,LinearMap.comp_apply,Finsupp.lapply_apply,mul_assoc]

theorem fullHighestRankReduction_highest_first_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hm : m≤c) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    physicalHighestFirstBoundary 1 l m (h+n-1) c
      (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank v).val =
      (quantumCupRankNormalization q hq n hn l m h c hadm * q^(-((n-1:ℕ):ℤ)*(m:ℤ))) *
        physicalHighestFirstBoundary n l m h c v.val := by
  unfold fullPhysicalHighestRankReduction
  simp only [LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply]
  exact physicalCupUnitaryRankReduction_highest_first_boundary q hq n hn l m h c hm hadm _

end AMSPhysical
#print axioms AMSPhysical.fullHighestRankReduction_highest_first_boundary

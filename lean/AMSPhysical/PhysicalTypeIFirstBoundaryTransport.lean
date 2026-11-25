import RankTwoTypeIFirstBoundary
import PhysicalTypeICouplingVectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem physicalQuantumCupUnitaryRankReduction_first_boundary (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c)
    (v : physicalQuantumCupSpan q n l m h c) :
    physicalTypeIFirstBoundary 1 l m (h+n-1) c
      (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm v).val =
      quantumCupRankNormalization q hq n hn l m h c hadm * quantumCupRankGauge n m *
        physicalTypeIFirstBoundary n l m h c v.val := by
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
  change cupFirstBoundaryEval q 1 l m (h+n-1) c
    (quantumCupUnitaryRankReduction q hq n hn l m h c hadm
      (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v)) = _
  rw [quantumCupUnitaryRankReduction_apply,map_smul,smul_eq_mul,
    quantumCupRankReduction_first_boundary q hq n hn]
  change _ * (_ * (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v).val _) = _
  rw [physicalQuantumCupCoefficientEquiv_literal]
  simp only [physicalTypeIFirstBoundary,LinearMap.comp_apply,Finsupp.lapply_apply,mul_assoc]

theorem fullPhysicalHighestRankReduction_first_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    physicalTypeIFirstBoundary 1 l m (h+n-1) c
      (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank v).val =
      quantumCupRankNormalization q hq n hn l m h c hadm * quantumCupRankGauge n m *
        physicalTypeIFirstBoundary n l m h c v.val := by
  unfold fullPhysicalHighestRankReduction
  simp only [LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply]
  exact physicalQuantumCupUnitaryRankReduction_first_boundary q hq n hn l m h c hadm _

theorem physicalTypeIRightCoupling_first_boundary_transport (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (t : QuantumCupIndex l m c) :
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+(h+n-1)))).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (standardCupRightHighest q hq hq1 l m (h+n-1) c hadm t).val ((0,⟨m,by omega⟩),0) =
      quantumCupRankNormalization q hq n hn l m h c hadm * quantumCupRankGauge n m *
        physicalTypeIFirstBoundary n l m h c
          (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val := by
  have he:=fullPhysicalHighestRankReduction_first_boundary q hq hq1 n hn l m h c hadm hRank
    (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)
  rw [physicalTypeIRightCoupling_rank_image,rankTwoHighestEquiv_literal,
    rankTwoMixedTripleEquiv_first_boundary] at he
  exact he

theorem physicalTypeILeftCoupling_first_boundary_transport (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (t : QuantumCupIndex l m c) :
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+(h+n-1)))).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (standardCupLeftHighest q hq hq1 l m (h+n-1) c hadm t).val ((0,⟨m,by omega⟩),0) =
      quantumCupRankNormalization q hq n hn l m h c hadm * quantumCupRankGauge n m *
        physicalTypeIFirstBoundary n l m h c
          (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val := by
  have he:=fullPhysicalHighestRankReduction_first_boundary q hq hq1 n hn l m h c hadm hRank
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t)
  rw [physicalTypeILeftCoupling_rank_image,rankTwoHighestEquiv_literal,
    rankTwoMixedTripleEquiv_first_boundary] at he
  exact he

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIRightCoupling_first_boundary_transport

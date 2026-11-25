import TwoVertexMetric
import QuantumTypeACompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem twoVertexEmbedding_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (L : ℕ) (v w : finiteWeightSpace (K:=ℝ) L) :
    occupationCompactBilin q n L (twoVertexEmbedding n hn L v) (twoVertexEmbedding n hn L w)=
      quantumBilin q L v w := by
  have hMaps : ((occupationCompactBilin q n L).comp (twoVertexEmbedding n hn L)).compl₂
      (twoVertexEmbedding n hn L)=quantumBilin q L := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro i
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro j
    change occupationCompactBilin q n L
      (twoVertexEmbedding n hn L (standardWeightBasis (K:=ℝ) L i))
      (twoVertexEmbedding n hn L (standardWeightBasis (K:=ℝ) L j))=_
    rw [twoVertexEmbedding_basis,twoVertexEmbedding_basis]
    change finiteWeightedPair (occupationCompactWeight q n L)
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
      (quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L i))
      (quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L j))=
      finiteWeightedPair (fun k : Fin (L+1) => quantumWeight q L k.val)
        (standardWeightBasis (K:=ℝ) L).equivFun.toLinearMap
        (standardWeightBasis (K:=ℝ) L i) (standardWeightBasis (K:=ℝ) L j)
    rw [finiteWeightedPair_basis,finiteWeightedPair_basis]
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,if_pos rfl,twoVertexOccupation_weight q hq hq1]
    · have hne : twoVertexOccupation n hn L i≠twoVertexOccupation n hn L j :=
        fun he => hij (twoVertexOccupation_injective n hn L he)
      rw [if_neg hne,if_neg hij]
  exact DFunLike.congr_fun (DFunLike.congr_fun hMaps v) w

end AMSPhysical

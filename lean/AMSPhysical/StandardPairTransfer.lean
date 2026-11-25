import StandardClebschAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Independent standard partial channel isometry. Source and target
pairs may have different determinant backgrounds, but share the actual
sl2 irreducible label. -/
def standardPairTransfer (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ) (r:Fin (min l m+1))
    (l' m':ℕ) (s:Fin (min l' m'+1)) (L:ℕ)
    (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L) :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) l' ⊗[ℝ] finiteWeightSpace (K:=ℝ) m') :=
  (standardClebschAtLabel q hq hq1 l' m' s L hs).comp
    (standardClebschAdjoint q hq hq1 l m r L hr)

theorem standardPairTransfer_selected (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ) (r:Fin (min l m+1))
    (l' m':ℕ) (s:Fin (min l' m'+1)) (L:ℕ)
    (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L) (v:finiteWeightSpace (K:=ℝ) L) :
    standardPairTransfer q hq hq1 l m r l' m' s L hr hs (standardClebschAtLabel q hq hq1 l m r L hr v)=
      standardClebschAtLabel q hq hq1 l' m' s L hs v := by
  simp only [standardPairTransfer,LinearMap.comp_apply,standardClebschAdjoint_selected]

theorem standardPairTransfer_other (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ) (r t:Fin (min l m+1)) (hrt:r≠t)
    (l' m':ℕ) (s:Fin (min l' m'+1)) (L:ℕ)
    (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L) (v:finiteWeightSpace (K:=ℝ) (coupledLabel l m t)) :
    standardPairTransfer q hq hq1 l m r l' m' s L hr hs (unitaryQuantumClebschMap q hq hq1 l m t v)=0 := by
  simp only [standardPairTransfer,LinearMap.comp_apply,standardClebschAdjoint_other q hq hq1 l m r t hrt,map_zero]

theorem standardPairTransfer_expansion (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ) (r:Fin (min l m+1))
    (l' m':ℕ) (s:Fin (min l' m'+1)) (L:ℕ)
    (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L)
    (v:finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    standardPairTransfer q hq hq1 l m r l' m' s L hr hs v=
      ∑ k:Fin (L+1),
        (quantumTensorBilin q l m (standardClebschAtLabel q hq hq1 l m r L hr (standardWeightBasis L k)) v/
          quantumWeight q L k.val) •
        standardClebschAtLabel q hq hq1 l' m' s L hs (standardWeightBasis L k) := by
  have he:=congrArg (standardClebschAtLabel q hq hq1 l' m' s L hs)
    ((standardWeightBasis (K:=ℝ) L).sum_repr (standardClebschAdjoint q hq hq1 l m r L hr v))
  simp only [map_sum,map_smul,standardClebschAdjoint_coordinate] at he
  exact he.symm

end AMSPhysical
#print axioms AMSPhysical.standardPairTransfer_expansion

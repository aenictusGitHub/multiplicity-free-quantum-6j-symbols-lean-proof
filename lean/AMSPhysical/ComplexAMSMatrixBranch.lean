import ComplexAMSCanonicalBranch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open Set
open scoped Topology
variable {I J:Type*} [Fintype I] [Fintype J]

/-- One common branch for the ENTIRE recoupling matrix, so continuation
never substitutes unrelated signs for individual entries. -/
def complexAMSMatrixCommonBranch (F G:I → J → ℂ → ℂ):Set ℂ:=
  connectedComponentIn (⋂ i:I,⋂ j:J,
    ({z:ℂ|AnalyticAt ℂ (F i j) z} ∩ {z:ℂ|AnalyticAt ℂ (G i j) z})) (2:ℂ)

theorem complexAMSMatrixCommonBranch_isOpen (F G:I → J → ℂ → ℂ):
    IsOpen (complexAMSMatrixCommonBranch F G):=by
  apply IsOpen.connectedComponentIn
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_analyticAt ℂ (F i j)).inter (isOpen_analyticAt ℂ (G i j))

theorem complexAMSMatrixCommonBranch_positive (F G:I → J → ℂ → ℂ)
    (hf:∀ i j,∀ q:ℝ,0<q → AnalyticAt ℂ (F i j) (q:ℂ))
    (hg:∀ i j,∀ q:ℝ,0<q → AnalyticAt ℂ (G i j) (q:ℂ)) (q:ℝ) (hq:0<q):
    (q:ℂ)∈complexAMSMatrixCommonBranch F G:=by
  have hc:IsPreconnected ((fun x:ℝ=>(x:ℂ)) '' Ioi 0):=
    isPreconnected_Ioi.image _ Complex.continuous_ofReal.continuousOn
  have h2:(2:ℂ)∈((fun x:ℝ=>(x:ℂ)) '' Ioi 0):=⟨2,by norm_num,by norm_num⟩
  apply (hc.subset_connectedComponentIn h2 ?_) ⟨q,hq,rfl⟩
  rintro z ⟨x,hx,rfl⟩
  simp only [Set.mem_iInter,Set.mem_inter_iff,Set.mem_setOf_eq]
  intro i j
  exact ⟨hf i j x hx,hg i j x hx⟩

theorem complexAMSMatrixCommonBranch_eq (F G:I → J → ℂ → ℂ)
    (hf:∀ i j,∀ q:ℝ,0<q → AnalyticAt ℂ (F i j) (q:ℂ))
    (hg:∀ i j,∀ q:ℝ,0<q → AnalyticAt ℂ (G i j) (q:ℂ))
    (hreal:∀ i j,∀ q:ℝ,0<q → q≠1 → F i j q=G i j q):
    ∀ i j,Set.EqOn (F i j) (G i j) (complexAMSMatrixCommonBranch F G):=by
  intro i j
  apply complexAnalytic_eqOn_of_positive_real (F i j) (G i j) _
    (complexAMSMatrixCommonBranch_isOpen F G) isPreconnected_connectedComponentIn
    (complexAMSMatrixCommonBranch_positive F G hf hg 2 (by norm_num))
  · intro z hz
    have hl:=connectedComponentIn_subset _ _ hz
    simp only [Set.mem_iInter,Set.mem_inter_iff,Set.mem_setOf_eq] at hl
    exact (hl i j).1
  · intro z hz
    have hl:=connectedComponentIn_subset _ _ hz
    simp only [Set.mem_iInter,Set.mem_inter_iff,Set.mem_setOf_eq] at hl
    exact (hl i j).2
  · intro q hq hq1 hmem
    exact hreal i j q hq hq1

end AMSPhysical
#print axioms AMSPhysical.complexAMSMatrixCommonBranch_eq

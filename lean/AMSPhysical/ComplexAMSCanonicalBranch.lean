import ComplexPhysicalAnalytic
import ComplexAMSExpression
import ComplexPhysicalIdentityPrinciple
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open Set
open scoped Topology

def complexAMSCommonBranch (f g:ℂ → ℂ):Set ℂ:=
  connectedComponentIn ({z:ℂ|AnalyticAt ℂ f z} ∩ {z:ℂ|AnalyticAt ℂ g z}) (2:ℂ)

theorem complexAMSCommonBranch_isOpen (f g:ℂ → ℂ):IsOpen (complexAMSCommonBranch f g):=
  ((isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)).connectedComponentIn

theorem complexAMSCommonBranch_positive (f g:ℂ → ℂ)
    (hf:∀ q:ℝ,0<q → AnalyticAt ℂ f (q:ℂ)) (hg:∀ q:ℝ,0<q → AnalyticAt ℂ g (q:ℂ))
    (q:ℝ) (hq:0<q):(q:ℂ)∈complexAMSCommonBranch f g:=by
  have hc:IsPreconnected ((fun x:ℝ=>(x:ℂ)) '' Ioi 0):=
    isPreconnected_Ioi.image _ Complex.continuous_ofReal.continuousOn
  have h2:(2:ℂ)∈((fun x:ℝ=>(x:ℂ)) '' Ioi 0):=⟨2,by norm_num,by norm_num⟩
  have hsub:((fun x:ℝ=>(x:ℂ)) '' Ioi 0)⊆({z:ℂ|AnalyticAt ℂ f z} ∩ {z:ℂ|AnalyticAt ℂ g z}):=by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨hf x hx,hg x hx⟩
  exact (hc.subset_connectedComponentIn h2 hsub) ⟨q,hq,rfl⟩

/-- A concrete nonempty connected complex branch of the independent
physical and AMS expressions, containing the ENTIRE positive real axis. -/
theorem complexAMSCommonBranch_eq (f g:ℂ → ℂ)
    (hf:∀ q:ℝ,0<q → AnalyticAt ℂ f (q:ℂ)) (hg:∀ q:ℝ,0<q → AnalyticAt ℂ g (q:ℂ))
    (hreal:∀ q:ℝ,0<q → q≠1 → f q=g q):
    Set.EqOn f g (complexAMSCommonBranch f g):=by
  apply complexAnalytic_eqOn_of_positive_real f g _ (complexAMSCommonBranch_isOpen f g)
    isPreconnected_connectedComponentIn (complexAMSCommonBranch_positive f g hf hg 2 (by norm_num))
  · intro z hz
    exact (connectedComponentIn_subset _ _ hz).1
  · intro z hz
    exact (connectedComponentIn_subset _ _ hz).2
  · intro q hq hq1 hmem
    exact hreal q hq hq1

/-- Native finite CG-tree continuation of the physical Type-I coefficient
satisfies the exact complex AMS formula on its constructed canonical branch.
No holomorphy or positive-real agreement hypothesis is left unproved. -/
theorem complexPhysicalTypeI_AMS_canonical_branch (h l m c:ℕ) (hadm:m≤l+c)
    (s t:QuantumCupIndex l m c):
    Set.EqOn (fun z:ℂ=>complexPhysicalTypeIWigner z h l m c s t)
      (fun z:ℂ=>complexAMSExpression z h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val))
      (complexAMSCommonBranch (fun z=>complexPhysicalTypeIWigner z h l m c s t)
        (fun z=>complexAMSExpression z h false (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val))):=by
  apply complexAMSCommonBranch_eq
  · intro q hq
    exact complexPhysicalTypeIWigner_analyticAt_positive q hq h l m c s t
  · intro q hq
    exact complexAMSExpression_analyticAt_positive q hq _ _ _ _ _ _ _ _
  · intro q hq hq1
    rw [complexPhysicalTypeIWigner_ofReal_actual q hq hq1 h l m c hadm,
      complexAMSExpression_ofReal q hq,physicalTypeI_AMS_Eq35_four_triangles q hq hq1]

theorem complexPhysicalTypeII_AMS_canonical_branch (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    Set.EqOn (fun z:ℂ=>complexPhysicalTypeIIWigner z h a b c d hbal r t)
      (fun z:ℂ=>complexAMSExpression z h true (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val))
      (complexAMSCommonBranch (fun z=>complexPhysicalTypeIIWigner z h a b c d hbal r t)
        (fun z=>complexAMSExpression z h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val))):=by
  apply complexAMSCommonBranch_eq
  · intro q hq
    exact complexPhysicalTypeIIWigner_analyticAt_positive q hq h a b c d hbal r t
  · intro q hq
    exact complexAMSExpression_analyticAt_positive q hq _ _ _ _ _ _ _ _
  · intro q hq hq1
    rw [complexPhysicalTypeIIWigner_ofReal_actual q hq hq1,
      complexAMSExpression_ofReal q hq,physicalTypeII_AMS_Eq35_calibrated q hq hq1]

end AMSPhysical
#print axioms AMSPhysical.complexPhysicalTypeII_AMS_canonical_branch

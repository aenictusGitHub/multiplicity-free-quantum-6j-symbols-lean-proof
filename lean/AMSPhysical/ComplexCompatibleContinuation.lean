import ComplexAMSMatrixBranch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology

/-- A whole-matrix holomorphic patch. The two matrix families are specified
independently; no equality between them is a field of this structure. -/
structure ComplexCoefficientPatch (I J:Type*) where
  domain:Set ℂ
  isOpen:IsOpen domain
  connected:IsPreconnected domain
  physical:I → J → ℂ → ℂ
  formula:I → J → ℂ → ℂ
  physical_analytic:∀ i j,AnalyticOnNhd ℂ (physical i j) domain
  formula_analytic:∀ i j,AnalyticOnNhd ℂ (formula i j) domain

variable {I J:Type*}

/-- Compatibility means continuation of EACH independently specified family
on a nonempty open overlap. It never assumes physical = formula. -/
def ComplexPatchContinues (p q:ComplexCoefficientPatch I J):Prop:=
  (p.domain ∩ q.domain).Nonempty ∧
    (∀ i j,Set.EqOn (p.physical i j) (q.physical i j) (p.domain ∩ q.domain)) ∧
    (∀ i j,Set.EqOn (p.formula i j) (q.formula i j) (p.domain ∩ q.domain))

theorem complexPatchContinues_preserves_eq (p q:ComplexCoefficientPatch I J)
    (h:ComplexPatchContinues p q)
    (he:∀ i j,Set.EqOn (p.physical i j) (p.formula i j) p.domain):
    ∀ i j,Set.EqOn (q.physical i j) (q.formula i j) q.domain:=by
  obtain ⟨z,hzp,hzq⟩:=h.1
  intro i j
  apply (q.physical_analytic i j).eqOn_of_preconnected_of_eventuallyEq (q.formula_analytic i j)
    q.connected hzq
  filter_upwards [(p.isOpen.inter q.isOpen).mem_nhds ⟨hzp,hzq⟩] with w hw
  rw [← h.2.1 i j hw,← h.2.2 i j hw]
  exact he i j hw.1

/-- Finite analytic continuation from the independently constructed base
families. Initial agreement is within each family separately. -/
inductive ComplexCompatibleContinuation (F G:I → J → ℂ → ℂ) (U:Set ℂ):ComplexCoefficientPatch I J → Prop
  | start (p:ComplexCoefficientPatch I J) (hU:p.domain⊆U)
      (hp:∀ i j,Set.EqOn (p.physical i j) (F i j) p.domain)
      (hg:∀ i j,Set.EqOn (p.formula i j) (G i j) p.domain):ComplexCompatibleContinuation F G U p
  | next (p q:ComplexCoefficientPatch I J) (hp:ComplexCompatibleContinuation F G U p)
      (hstep:ComplexPatchContinues p q):ComplexCompatibleContinuation F G U q

theorem complexCompatibleContinuation_eq (F G:I → J → ℂ → ℂ) (U:Set ℂ)
    (hbase:∀ i j,Set.EqOn (F i j) (G i j) U) (p:ComplexCoefficientPatch I J)
    (h:ComplexCompatibleContinuation F G U p):
    ∀ i j,Set.EqOn (p.physical i j) (p.formula i j) p.domain:=by
  induction h with
  | start p hU hp hg=>
    intro i j z hz
    rw [hp i j hz,hg i j hz]
    exact hbase i j (hU hz)
  | next p q hp hstep ih=>exact complexPatchContinues_preserves_eq p q hstep ih

variable [Fintype I] [Fintype J]

/-- The concrete base patch is constructed on a common nonempty branch of
all entries. Analyticity follows from the explicitly defined analytic locus. -/
def complexAMSCanonicalPatch (F G:I → J → ℂ → ℂ):ComplexCoefficientPatch I J where
  domain:=complexAMSMatrixCommonBranch F G
  isOpen:=complexAMSMatrixCommonBranch_isOpen F G
  connected:=isPreconnected_connectedComponentIn
  physical:=F
  formula:=G
  physical_analytic:=by
    intro i j z hz
    have hl:=connectedComponentIn_subset _ _ hz
    simp only [Set.mem_iInter,Set.mem_inter_iff,Set.mem_setOf_eq] at hl
    exact (hl i j).1
  formula_analytic:=by
    intro i j z hz
    have hl:=connectedComponentIn_subset _ _ hz
    simp only [Set.mem_iInter,Set.mem_inter_iff,Set.mem_setOf_eq] at hl
    exact (hl i j).2

theorem complexAMS_all_compatible_continuations (F G:I → J → ℂ → ℂ)
    (hf:∀ i j,∀ q:ℝ,0<q → AnalyticAt ℂ (F i j) (q:ℂ))
    (hg:∀ i j,∀ q:ℝ,0<q → AnalyticAt ℂ (G i j) (q:ℂ))
    (hreal:∀ i j,∀ q:ℝ,0<q → q≠1 → F i j q=G i j q)
    (p:ComplexCoefficientPatch I J)
    (h:ComplexCompatibleContinuation F G (complexAMSMatrixCommonBranch F G) p):
    ∀ i j,Set.EqOn (p.physical i j) (p.formula i j) p.domain:=
  complexCompatibleContinuation_eq F G _ (complexAMSMatrixCommonBranch_eq F G hf hg hreal) p h

end AMSPhysical
#print axioms AMSPhysical.complexAMS_all_compatible_continuations

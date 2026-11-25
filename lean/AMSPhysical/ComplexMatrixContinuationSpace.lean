import ComplexAMSMatrixBranch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set

/-- A holomorphic branch of ONE whole coefficient matrix. Its definition
contains neither an AMS formula nor an equality with another matrix. -/
structure HolomorphicMatrixPatch (I J:Type*) where
  domain:Set ℂ
  isOpen:IsOpen domain
  connected:IsPreconnected domain
  value:I → J → ℂ → ℂ
  analytic:∀ i j,AnalyticOnNhd ℂ (value i j) domain

variable {I J:Type*}

def MatrixPatchOverlap (p q:HolomorphicMatrixPatch I J):Prop:=
  (p.domain ∩ q.domain).Nonempty ∧
    ∀ i j,Set.EqOn (p.value i j) (q.value i j) (p.domain ∩ q.domain)

/-- Analytic continuation of one independently specified base matrix.
There is no second matrix or comparison hypothesis in this definition. -/
inductive IsMatrixContinuation (F:I → J → ℂ → ℂ) (U:Set ℂ):HolomorphicMatrixPatch I J → Prop
  | start (p:HolomorphicMatrixPatch I J) (hU:p.domain⊆U)
      (hF:∀ i j,Set.EqOn (p.value i j) (F i j) p.domain):IsMatrixContinuation F U p
  | next (p q:HolomorphicMatrixPatch I J) (hp:IsMatrixContinuation F U p)
      (hstep:MatrixPatchOverlap p q):IsMatrixContinuation F U q

theorem IsMatrixContinuation.change_base (F G:I → J → ℂ → ℂ) (U:Set ℂ)
    (hFG:∀ i j,Set.EqOn (F i j) (G i j) U) (p:HolomorphicMatrixPatch I J)
    (h:IsMatrixContinuation F U p):IsMatrixContinuation G U p:=by
  induction h with
  | start p hU hF=>
    apply IsMatrixContinuation.start p hU
    intro i j z hz
    exact (hF i j hz).trans (hFG i j (hU hz))
  | next p q hp hs ih=>exact IsMatrixContinuation.next p q ih hs

/-- Equality of the full maximal analytic continuations, preserving the
same patch chain and the entire matrix; no independent entry signs arise. -/
theorem matrixContinuation_same_germ (F G:I → J → ℂ → ℂ) (U:Set ℂ)
    (hFG:∀ i j,Set.EqOn (F i j) (G i j) U) (p:HolomorphicMatrixPatch I J):
    IsMatrixContinuation F U p ↔ IsMatrixContinuation G U p:=
  ⟨IsMatrixContinuation.change_base F G U hFG p,
    IsMatrixContinuation.change_base G F U (fun i j=>Set.EqOn.symm (hFG i j)) p⟩

/-- A value of a generic complex coefficient matrix is a value of its
analytic continuation from the physical base branch. This definition does
not mention another family or an AMS expression. -/
def HasMatrixContinuationValue (F:I → J → ℂ → ℂ) (U:Set ℂ) (q:ℂ) (v:I → J → ℂ):Prop:=
  ∃ p:HolomorphicMatrixPatch I J,IsMatrixContinuation F U p ∧ q∈p.domain ∧
    ∀ i j,p.value i j q=v i j

theorem matrixContinuationValues_same_germ (F G:I → J → ℂ → ℂ) (U:Set ℂ)
    (hFG:∀ i j,Set.EqOn (F i j) (G i j) U) (q:ℂ) (v:I → J → ℂ):
    HasMatrixContinuationValue F U q v ↔ HasMatrixContinuationValue G U q v:=by
  constructor
  · rintro ⟨p,hp,hq,hv⟩
    exact ⟨p,(matrixContinuation_same_germ F G U hFG p).mp hp,hq,hv⟩
  · rintro ⟨p,hp,hq,hv⟩
    exact ⟨p,(matrixContinuation_same_germ F G U hFG p).mpr hp,hq,hv⟩

end AMSPhysical
#print axioms AMSPhysical.matrixContinuationValues_same_germ

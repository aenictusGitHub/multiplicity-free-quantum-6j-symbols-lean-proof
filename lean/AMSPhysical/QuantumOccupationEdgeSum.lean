import QuantumOccupationEdges

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Exact finite cancellation along every nonzero raising/lowering edge. -/
theorem occupation_edge_sum {A : Type*} [AddCommGroup A] (n r : ℕ) (i : Fin n)
    (f g : occupationWeights (Fin (n+1)) r → A)
    (hf : ∀ x,x.val i.succ=0 → f x=0)
    (hg : ∀ x,x.val i.castSucc=0 → g x=0)
    (he : ∀ x (hi : 0<x.val i.succ),f x+g (raisedOccupation n r x i hi)=0) :
    (∑ x,f x)+(∑ x,g x)=0 := by
  classical
  have hf' : (∑ x,f x)=∑ x : occupationRaisingEdges n r i,f x.val := by
    apply Finset.sum_congr_set {x | 0<x.val i.succ} f (fun x => f x.val)
    · intro x hx
      rfl
    · intro x hx
      change ¬0<x.val i.succ at hx
      have hnonneg := x.property.1 i.succ
      exact hf x (by omega)
  have hg' : (∑ x,g x)=∑ x : occupationLoweringEdges n r i,g x.val := by
    apply Finset.sum_congr_set {x | 0<x.val i.castSucc} g (fun x => g x.val)
    · intro x hx
      rfl
    · intro x hx
      change ¬0<x.val i.castSucc at hx
      have hnonneg := x.property.1 i.castSucc
      exact hg x (by omega)
  rw [hf',hg',← (occupationEdgeEquiv n r i).sum_comp (fun x => g x.val),← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x hx
  exact he x.val x.property

end AMSPhysical
#print axioms AMSPhysical.occupation_edge_sum

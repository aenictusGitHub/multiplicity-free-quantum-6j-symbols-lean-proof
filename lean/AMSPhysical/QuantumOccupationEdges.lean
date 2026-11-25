import QuantumOccupationLowering

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def occupationRaisingEdges (n r : ℕ) (i : Fin n) :=
  {x : occupationWeights (Fin (n+1)) r // 0<x.val i.succ}
def occupationLoweringEdges (n r : ℕ) (i : Fin n) :=
  {x : occupationWeights (Fin (n+1)) r // 0<x.val i.castSucc}

noncomputable instance occupationRaisingEdges_fintype (n r : ℕ) (i : Fin n) :
    Fintype (occupationRaisingEdges n r i) := by
  unfold occupationRaisingEdges
  infer_instance
noncomputable instance occupationLoweringEdges_fintype (n r : ℕ) (i : Fin n) :
    Fintype (occupationLoweringEdges n r i) := by
  unfold occupationLoweringEdges
  infer_instance

/-- The nonzero raising and lowering edges are in exact bijection, including
all boundaries of the finite occupation simplex. -/
def occupationEdgeEquiv (n r : ℕ) (i : Fin n) :
    occupationRaisingEdges n r i ≃ occupationLoweringEdges n r i where
  toFun x := ⟨raisedOccupation n r x.val i x.property,by
    rw [raisedOccupation_target]
    have hn := x.val.property.1 i.castSucc
    omega⟩
  invFun y := ⟨loweredOccupation n r y.val i y.property,loweredOccupation_source_positive n r y.val i y.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val+latticeRoot i.castSucc i.succ+latticeRoot i.succ i.castSucc=x.val.val
    rw [latticeRoot_swap]
    abel
  right_inv y := by
    apply Subtype.ext
    exact raised_loweredOccupation n r y.val i y.property

end AMSPhysical
#print axioms AMSPhysical.occupationEdgeEquiv

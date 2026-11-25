import QuantumChannelNeighbors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

/-- Every nonempty physical channel interval has its required extremal row;
the initial row in the recoupling evaluation always exists. -/
theorem fixedLeftHighest_first_exists (l m n H : ℕ) (p : FixedLeftHighest l m n H) :
    ∃ first : FixedLeftHighest l m n H,first.val.1.val=0 ∨ first.val.2.val=n := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hi := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hd := fixedLeftHighest_defect l m n H p
  have hmin : leftHighestDefect l m n H-n≤p.val.1.val := by omega
  have hsum : leftHighestDefect l m n H+p.val.1.val≤l+m := by unfold coupledLabel at hi;omega
  let r : Fin (min l m+1) := ⟨leftHighestDefect l m n H-n,by omega⟩
  have hsI : leftHighestDefect l m n H-r.val≤coupledLabel l m r := by
    dsimp [r]
    unfold coupledLabel
    omega
  have hsN : leftHighestDefect l m n H-r.val≤n := by dsimp [r];omega
  let s : Fin (min (coupledLabel l m r) n+1) := ⟨leftHighestDefect l m n H-r.val,
    Nat.lt_succ_iff.mpr (le_min hsI hsN)⟩
  let a : LeftHighestPath l m n := ⟨r,s⟩
  have ht : leftTotalLabel l m n a=H := by
    have h₁ := leftTotalLabel_defect l m n p.val
    have h₂ := leftTotalLabel_defect l m n a
    rw [p.property] at h₁
    change l+m+n=leftTotalLabel l m n a+2*((leftHighestDefect l m n H-n)+
      (leftHighestDefect l m n H-(leftHighestDefect l m n H-n))) at h₂
    omega
  refine ⟨⟨a,ht⟩,?_⟩
  change leftHighestDefect l m n H-n=0 ∨
    leftHighestDefect l m n H-(leftHighestDefect l m n H-n)=n
  omega

end AMSPhysical

#print axioms AMSPhysical.fixedLeftHighest_first_exists

import QuantumFixedHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

/-- Every nonboundary left channel has the preceding admissible channel. -/
theorem fixedLeftHighest_previous (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (hr : 0<p.val.1.val) (hs : p.val.2.val<n) :
    ∃ v : FixedLeftHighest l m n H,v.val.1.val+1=p.val.1.val := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hi := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  let r : Fin (min l m+1) := ⟨p.val.1.val-1,by have hh := p.val.1.isLt;omega⟩
  have hib : p.val.2.val+1≤coupledLabel l m r := by
    dsimp [r]
    unfold coupledLabel at *
    omega
  let s : Fin (min (coupledLabel l m r) n+1) := ⟨p.val.2.val+1,
    Nat.lt_succ_iff.mpr (le_min hib (by omega))⟩
  let a : LeftHighestPath l m n := ⟨r,s⟩
  have htotal : leftTotalLabel l m n a=H := by
    have h₁ := leftTotalLabel_defect l m n p.val
    have h₂ := leftTotalLabel_defect l m n a
    rw [p.property] at h₁
    change l+m+n=leftTotalLabel l m n a+2*((p.val.1.val-1)+(p.val.2.val+1)) at h₂
    omega
  exact ⟨⟨a,htotal⟩,by change p.val.1.val-1+1=p.val.1.val;omega⟩

theorem fixedLeftHighest_previous_second (l m n H : ℕ) (p v : FixedLeftHighest l m n H)
    (hnext : v.val.1.val+1=p.val.1.val) : v.val.2.val=p.val.2.val+1 := by
  have hp := fixedLeftHighest_defect l m n H p
  have hv := fixedLeftHighest_defect l m n H v
  omega

theorem fixedLeftHighest_boundary_minimal (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (hbound : p.val.1.val=0 ∨ p.val.2.val=n) :
    ∀ v : FixedLeftHighest l m n H,p.val.1.val≤v.val.1.val := by
  intro v
  rcases hbound with hr | hs
  · omega
  · have hp := fixedLeftHighest_defect l m n H p
    have hv := fixedLeftHighest_defect l m n H v
    have hn := channel_right_bound (coupledLabel l m v.val.1) n v.val.2
    omega

end AMSPhysical

#print axioms AMSPhysical.fixedLeftHighest_previous

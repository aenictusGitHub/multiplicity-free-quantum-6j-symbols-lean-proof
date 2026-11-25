import QuantumOccupationGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

/-- A nonvanishing coefficient solution on the connected occupation graph is
unique up to one scalar, including every boundary of the simplex. -/
theorem occupation_scalar_unique (n r : ℕ) (f c : occupationWeights (Fin (n+1)) r → K)
    (hc : ∀ x,c x≠0)
    (he : ∀ x (i : Fin n) (hi : 0<x.val i.succ),
      f (raisedOccupation n r x i hi)*c x=f x*c (raisedOccupation n r x i hi)) :
    ∀ x,f x=(f (highestOccupation n r)/c (highestOccupation n r))*c x := by
  let s := f (highestOccupation n r)/c (highestOccupation n r)
  have hs : f (highestOccupation n r)=s*c (highestOccupation n r) := by
    dsimp [s]
    rw [div_mul_cancel₀ _ (hc _)]
  have aux : ∀ k,∀ x : occupationWeights (Fin (n+1)) r,occupationHeight n r x=k → f x=s*c x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx
      by_cases hh : x=highestOccupation n r
      · simpa only [hh] using hs
      · obtain ⟨i,hi⟩ := occupation_nonhighest_donor n r x hh
        have hheight := raisedOccupation_height n r x i hi
        have hnext := ih (occupationHeight n r (raisedOccupation n r x i hi)) (by omega)
          (raisedOccupation n r x i hi) rfl
        have hed := he x i hi
        rw [hnext] at hed
        apply mul_right_cancel₀ (hc (raisedOccupation n r x i hi))
        calc
          _ = (s*c (raisedOccupation n r x i hi))*c x := hed.symm
          _ = _ := by ring
  intro x
  exact aux (occupationHeight n r x) x rfl

end AMSPhysical
#print axioms AMSPhysical.occupation_scalar_unique

import JacobiEigenvectorUniqueness

set_option autoImplicit false
noncomputable section
namespace AMSPhysical

/-- A first-order neighboring recurrence and one initial value uniquely
fix a scalar function on any finite connected channel interval. -/
theorem first_order_grid_unique {ι : Type*} (index : ι → ℕ) (first : ι)
    (d : ι → ℝ) (A : ι → ι → ℝ)
    (hprev : ∀ i,i≠first → ∃ j,index j+1=index i ∧ d i≠0)
    (f g : ι → ℝ)
    (hf : ∀ i j,index j+1=index i → d i*f i=A i j*f j)
    (hg : ∀ i j,index j+1=index i → d i*g i=A i j*g j)
    (hfirst : f first=g first) : f=g := by
  have aux : ∀ n,∀ i,index i=n → f i=g i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin
      by_cases hi : i=first
      · simpa only [hi] using hfirst
      · obtain ⟨j,hji,hd⟩ := hprev i hi
        have hj : f j=g j := ih (index j) (by omega) j rfl
        apply mul_left_cancel₀ hd
        rw [hf i j hji,hg i j hji,hj]
  funext i
  exact aux (index i) i rfl

end AMSPhysical

#print axioms AMSPhysical.first_order_grid_unique

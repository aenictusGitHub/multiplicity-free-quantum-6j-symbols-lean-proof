import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
variable {V X I : Type*} [AddCommGroup V] [Module ℝ V]

/-- A genuine bounded lowering filtration yields a common highest vector in
every nonzero invariant subspace. No semisimplicity or highest-vector
existence theorem is assumed; strict decrease proves termination. -/
theorem commonHighest_of_decreasing_coefficients
    (C : V →ₗ[ℝ] (X →₀ ℝ)) (hC : Function.Injective C) (g : X → ℤ)
    (T : I → Module.End ℝ V)
    (hNonneg : ∀ (v : V) (x : X),C v x≠0 → 0≤g x)
    (hDecrease : ∀ (i : I) (v : V) (k : ℕ),
      (∀ x,C v x≠0 → g x≤(k:ℤ)) → ∀ x,C (T i v) x≠0 → g x<(k:ℤ))
    (S : Submodule ℝ V) (hS : ∀ (i : I) (v : V),v∈S → T i v∈S)
    (k : ℕ) (v : V) (hv : v∈S) (hv0 : v≠0)
    (hBound : ∀ x,C v x≠0 → g x≤(k:ℤ)) :
    ∃ w : V,w∈S ∧ w≠0 ∧ ∀ i : I,T i w=0 := by
  classical
  induction k using Nat.strong_induction_on generalizing v with
  | h k ih =>
    by_cases hTop : ∀ i : I,T i v=0
    · exact ⟨v,hv,hv0,hTop⟩
    · push_neg at hTop
      obtain ⟨i,hi⟩ := hTop
      have hCv : C (T i v)≠0 := by
        intro hz
        apply hi
        apply hC
        simpa only [map_zero] using hz
      have hex : ∃ x,C (T i v) x≠0 := by
        by_contra hn
        push_neg at hn
        apply hCv
        ext x
        exact hn x
      obtain ⟨x,hx⟩ := hex
      have hk : 0<k := by
        have hn := hNonneg (T i v) x hx
        have hd := hDecrease i v k hBound x hx
        omega
      apply ih (k-1) (by omega) (T i v) (hS i v hv) hi
      intro x hx
      have hd := hDecrease i v k hBound x hx
      omega

end AMSPhysical

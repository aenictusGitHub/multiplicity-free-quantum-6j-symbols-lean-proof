import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An irreducible tridiagonal eigenvector is fixed by its first component.
The index set may be any finite contiguous set of integer channel labels. -/
theorem tridiagonal_eigenvector_unique (A : ι → ι → ℝ) (index : ι → ℕ)
    (hinj : Function.Injective index) (first : ι)
    (hupper : ∀ i j,index i+1< index j → A i j=0)
    (hprev : ∀ i,i≠first → ∃ j,index j+1=index i ∧ A j i≠0)
    (f g : ι → ℝ) (L : ℝ)
    (hf : ∀ i,(∑ j,A i j*f j)=L*f i)
    (hg : ∀ i,(∑ j,A i j*g j)=L*g i)
    (hfirst : f first=g first) : f=g := by
  have he (i : ι) : (∑ j,A i j*(f j-g j))=L*(f i-g i) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [hf i,hg i]
  have aux : ∀ n,∀ i,index i=n → f i=g i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin
      by_cases hi : i=first
      · simpa only [hi] using hfirst
      · obtain ⟨j,hji,hA⟩ := hprev i hi
        have hjn : index j<n := by omega
        have hj : f j=g j := ih (index j) hjn j rfl
        have hs : (∑ k,A j k*(f k-g k))=A j i*(f i-g i) := by
          apply Finset.sum_eq_single i
          · intro k hk hki
            by_cases hlt : index k<n
            · rw [ih (index k) hlt k rfl,sub_self,mul_zero]
            · have hgt : index j+1< index k := by
                have hne : index k≠n := fun h => hki (hinj (h.trans hin.symm))
                omega
              rw [hupper j k hgt,zero_mul]
          · simp
        have hrow := he j
        rw [hs,hj,sub_self,mul_zero] at hrow
        exact sub_eq_zero.mp ((mul_eq_zero.mp hrow).resolve_left hA)
  funext i
  exact aux (index i) i rfl

end AMSPhysical

#print axioms AMSPhysical.tridiagonal_eigenvector_unique

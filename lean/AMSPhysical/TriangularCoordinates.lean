import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

/-- Triangular coordinates recover all coefficients below a support cutoff. -/
theorem triangular_expansion_cutoff (b : ι → V) (index : ι → ℕ)
    (hinj : Function.Injective index) (coord : ℕ → V →ₗ[ℝ] ℝ)
    (htri : ∀ i y,y< index i → coord y (b i)=0)
    (hdiag : ∀ i,coord (index i) (b i)≠0)
    (c : ι → ℝ) (v : V) (hexp : (∑ i,c i • b i)=v)
    (cut : ℕ) (hzero : ∀ y,y<cut → coord y v=0) :
    ∀ i,index i<cut → c i=0 := by
  have aux : ∀ k,∀ i,index i=k → k<cut → c i=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik hkc
      have he := congrArg (coord k) hexp
      rw [map_sum] at he
      simp only [map_smul,smul_eq_mul] at he
      have hs : (∑ j,c j*coord k (b j))=c i*coord k (b i) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          by_cases hjk : index j<k
          · rw [ih (index j) hjk j rfl (lt_trans hjk hkc),zero_mul]
          · have hgt : k< index j := by
              have hne : index j≠k := fun h => hji (hinj (h.trans hik.symm))
              omega
            rw [htri j k hgt,mul_zero]
        · simp
      rw [hs,hzero k hkc] at he
      exact (mul_eq_zero.mp he).resolve_right (by simpa only [hik] using hdiag i)
  intro i hi
  exact aux (index i) i rfl hi

/-- The first potentially nonzero coordinate determines its expansion coefficient. -/
theorem triangular_expansion_leading (b : ι → V) (index : ι → ℕ)
    (hinj : Function.Injective index) (coord : ℕ → V →ₗ[ℝ] ℝ)
    (htri : ∀ i y,y< index i → coord y (b i)=0)
    (c : ι → ℝ) (v : V) (hexp : (∑ i,c i • b i)=v)
    (i : ι) (hsmall : ∀ j,index j< index i → c j=0) :
    coord (index i) v=c i*coord (index i) (b i) := by
  rw [← hexp,map_sum]
  simp only [map_smul,smul_eq_mul]
  apply Finset.sum_eq_single i
  · intro j hj hji
    by_cases hlt : index j< index i
    · rw [hsmall j hlt,zero_mul]
    · have hgt : index i< index j := by
        have hne : index j≠index i := fun h => hji (hinj h)
        omega
      rw [htri j (index i) hgt,mul_zero]
  · simp

/-- A symmetric Hessenberg matrix is tridiagonal. -/
theorem symmetric_hessenberg_tridiagonal (A : ι → ι → ℝ) (index : ι → ℕ)
    (hsym : ∀ i j,A i j=A j i)
    (hband : ∀ i j,index j+1< index i → A i j=0)
    (i j : ι) (hfar : index j+1< index i ∨ index i+1< index j) : A i j=0 := by
  rcases hfar with h | h
  · exact hband i j h
  · rw [hsym i j]
    exact hband j i h

end AMSPhysical

#print axioms AMSPhysical.triangular_expansion_cutoff

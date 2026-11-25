import BilinearAdjoint
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]

/-- Oppositely bidiagonal self-adjoint operators determine a bilinear form
from one edge norm. All recurrence, distinctness and nonzero-link hypotheses
are displayed, rather than replacing the physical operator calculation. -/
theorem bidiagonalPair_form_zero (b : Module.Basis I ℝ V) (index : I → ℕ)
    (hinj : Function.Injective index) (top : I) (hmax : ∀ i,index i ≤ index top)
    (next : ∀ i,i≠top → I) (hnext : ∀ i hi,index (next i hi)=index i+1)
    (A D : Module.End ℝ V) (a : I → ℝ) (u d v : I → ℝ)
    (hAtop : A (b top)=a top • b top)
    (hA : ∀ i hi,A (b i)=a i • b i+u i • b (next i hi))
    (ha : ∀ i,i≠top → a top≠a i)
    (hD : ∀ i hi,D (b (next i hi))=d i • b (next i hi)+v i • b i)
    (hv : ∀ i,i≠top → v i≠0)
    (H : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hHA : PairAdjoint H A A) (hHD : PairAdjoint H D D)
    (hNorm : H (b top) (b top)=0) : H=0 := by
  have hrow : ∀ k,∀ i,index top-index i=k → H (b top) (b i)=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      by_cases hi : i=top
      · subst i;exact hNorm
      · have hlt : index i < index top := by
          have hn : index i≠index top := fun he =>hi (hinj he)
          have hm:=hmax i
          omega
        have hj:=ih (index top-index (next i hi)) (by rw [hnext];omega) (next i hi) rfl
        have he:=hHA (b top) (b i)
        rw [hAtop,hA i hi] at he
        simp only [map_smul,LinearMap.smul_apply,map_add,LinearMap.add_apply,smul_eq_mul,hj,mul_zero,add_zero] at he
        have hz : (a top-a i)*H (b top) (b i)=0 := by nlinarith [he]
        exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (ha i hi))
  have htop : H (b top)=0 := by
    apply b.ext
    intro i
    exact hrow (index top-index i) i rfl
  have hall : ∀ k,∀ i,index top-index i=k → H (b i)=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      by_cases hi : i=top
      · subst i;exact htop
      · have hlt : index i < index top := by
          have hn : index i≠index top := fun he =>hi (hinj he)
          have hm:=hmax i
          omega
        have hj:=ih (index top-index (next i hi)) (by rw [hnext];omega) (next i hi) rfl
        apply LinearMap.ext
        intro w
        have he:=hHD (b (next i hi)) w
        rw [hD i hi] at he
        simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hj,
          LinearMap.zero_apply,mul_zero,zero_add] at he
        exact (mul_eq_zero.mp he).resolve_left (hv i hi)
  apply b.ext
  intro i
  exact hall (index top-index i) i rfl

end AMSPhysical

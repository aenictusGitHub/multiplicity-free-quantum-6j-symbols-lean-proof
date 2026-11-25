import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

/-- Interchange and translate the two indices in a finite triangular sum. -/
theorem sum_triangular_reindex (n : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range (n+1),∑ j ∈ Finset.range (k+1),f k j)=
      ∑ j ∈ Finset.range (n+1),∑ i ∈ Finset.range (n-j+1),f (j+i) j := by
  classical
  rw [Finset.sum_sigma',Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.2,p.1-p.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma,Finset.mem_range] at hp ⊢
    omega
  · intro p hp q hq he
    simp only [Finset.mem_sigma,Finset.mem_range] at hp hq
    have h₁ : p.2=q.2 := congrArg Sigma.fst he
    have h₂ : p.1-p.2=q.1-q.2 := congrArg Sigma.snd he
    have h₃ : p.1=q.1 := by omega
    cases p
    cases q
    simp_all
  · intro p hp
    simp only [Finset.mem_sigma,Finset.mem_range] at hp
    refine ⟨⟨p.1+p.2,p.1⟩,?_,?_⟩
    · simp only [Finset.mem_sigma,Finset.mem_range]
      omega
    · simp
  · intro p hp
    simp only [Finset.mem_sigma,Finset.mem_range] at hp
    change f p.1 p.2=f (p.2+(p.1-p.2)) p.2
    have he : p.2+(p.1-p.2)=p.1 := by omega
    rw [he]

end AMSPhysical

#print axioms AMSPhysical.sum_triangular_reindex

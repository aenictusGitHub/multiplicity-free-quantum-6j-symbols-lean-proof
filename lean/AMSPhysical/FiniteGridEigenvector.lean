import JacobiEigenvectorUniqueness

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_injective_grid_sum (index : ι → ℕ) (hinj : Function.Injective index)
    (F : ℤ → ℝ) (z : ℤ) (c : ℝ)
    (hmissing : (¬∃ j,(index j:ℤ)=z) → c*F z=0) :
    (∑ j,if (index j:ℤ)=z then c*F (index j) else 0)=c*F z := by
  classical
  by_cases he : ∃ j,(index j:ℤ)=z
  · obtain ⟨j,hj⟩ := he
    rw [Finset.sum_eq_single j]
    · rw [if_pos hj,hj]
    · intro k hk hkj
      apply if_neg
      intro hz
      apply hkj
      apply hinj
      omega
    · simp
  · rw [hmissing he]
    apply Finset.sum_eq_zero
    intro j hj
    apply if_neg
    exact fun hz => he ⟨j,hz⟩

/-- A birth/death grid solution becomes a symmetric Jacobi eigenvector after
any gauge satisfying the two neighboring coefficient identities. Missing grid
points are handled by explicit boundary conditions. -/
theorem finite_grid_eigenvector (A : ι → ι → ℝ) (index : ι → ℕ)
    (hinj : Function.Injective index) (w b d : ι → ℝ) (F : ℤ → ℝ) (L₀ L : ℝ)
    (hdiag : ∀ i,A i i=L₀-b i-d i)
    (hlower : ∀ i j,index j+1=index i → A i j*w j=d i*w i)
    (hupper : ∀ i j,index i+1=index j → A i j*w j=b i*w i)
    (hsupp : ∀ i j,index j+1≠index i → index i+1≠index j → i≠j → A i j=0)
    (hminus : ∀ i,(¬∃ j,index j+1=index i) → d i*F ((index i:ℤ)-1)=0)
    (hplus : ∀ i,(¬∃ j,index i+1=index j) → b i*F ((index i:ℤ)+1)=0)
    (hrec : ∀ i,b i*(F ((index i:ℤ)+1)-F (index i))+
      d i*(F ((index i:ℤ)-1)-F (index i))=(L-L₀)*F (index i)) :
    ∀ i,(∑ j,A i j*(w j*F (index j)))=L*(w i*F (index i)) := by
  classical
  intro i
  have hentry (j : ι) : A i j*(w j*F (index j))=
      (if (index j:ℤ)=(index i:ℤ) then (L₀-b i-d i)*w i*F (index j) else 0)+
      (if (index j:ℤ)=(index i:ℤ)-1 then d i*w i*F (index j) else 0)+
      (if (index j:ℤ)=(index i:ℤ)+1 then b i*w i*F (index j) else 0) := by
    by_cases hij : i=j
    · subst j
      rw [hdiag i,if_pos rfl,if_neg (by omega),if_neg (by omega)]
      ring
    · have hne : (index j:ℤ)≠(index i:ℤ) := by
        intro he
        exact hij (hinj (by omega))
      rw [if_neg hne]
      by_cases hm : index j+1=index i
      · rw [if_pos (by omega),if_neg (by omega),zero_add,add_zero,← mul_assoc,hlower i j hm]
      · rw [if_neg (by omega)]
        by_cases hp : index i+1=index j
        · rw [if_pos (by omega),zero_add,zero_add,← mul_assoc,hupper i j hp]
        · rw [if_neg (by omega),hsupp i j hm hp hij,zero_mul,zero_add,zero_add]
  simp_rw [hentry]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  rw [finite_injective_grid_sum index hinj F (index i) ((L₀-b i-d i)*w i)
    (fun hn => False.elim (hn ⟨i,rfl⟩))]
  have hmissingMinus : (¬∃ j,(index j:ℤ)=(index i:ℤ)-1) → (d i*w i)*F ((index i:ℤ)-1)=0 := by
    intro hn
    have hh : ¬∃ j,index j+1=index i := by rintro ⟨j,hj⟩;exact hn ⟨j,by omega⟩
    linear_combination w i*hminus i hh
  have hmissingPlus : (¬∃ j,(index j:ℤ)=(index i:ℤ)+1) → (b i*w i)*F ((index i:ℤ)+1)=0 := by
    intro hn
    have hh : ¬∃ j,index i+1=index j := by rintro ⟨j,hj⟩;exact hn ⟨j,by omega⟩
    linear_combination w i*hplus i hh
  rw [finite_injective_grid_sum index hinj F _ _ hmissingMinus,
    finite_injective_grid_sum index hinj F _ _ hmissingPlus]
  linear_combination w i*hrec i

end AMSPhysical

#print axioms AMSPhysical.finite_grid_eigenvector

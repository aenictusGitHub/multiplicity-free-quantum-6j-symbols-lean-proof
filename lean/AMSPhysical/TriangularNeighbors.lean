import TriangularCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

theorem triangular_expansion_two (b : ι → V) (index : ι → ℕ)
    (hinj : Function.Injective index) (coord : ℕ → V →ₗ[ℝ] ℝ)
    (htri : ∀ i y,y< index i → coord y (b i)=0)
    (c : ι → ℝ) (v : V) (hexp : (∑ i,c i • b i)=v)
    (i j : ι) (hnext : index j+1=index i)
    (hsmall : ∀ k,index k+1< index i → c k=0) :
    coord (index i) v=c i*coord (index i) (b i)+c j*coord (index i) (b j) := by
  classical
  have hij : i≠j := by intro he;rw [he] at hnext;omega
  rw [← hexp,map_sum]
  simp only [map_smul,smul_eq_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  congr 1
  apply Finset.sum_eq_single i
  · intro k hk hki
    have hkj : k≠j := (Finset.mem_erase.mp hk).1
    by_cases hlt : index k< index i
    · have hne : index k≠index j := fun h => hkj (hinj h)
      rw [hsmall k (by omega),zero_mul]
    · have hgt : index i< index k := by
        have hne : index k≠index i := fun h => hki (hinj h)
        omega
      rw [htri k (index i) hgt,mul_zero]
  · intro hi
    exact (hi (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩)).elim

end AMSPhysical

#print axioms AMSPhysical.triangular_expansion_two

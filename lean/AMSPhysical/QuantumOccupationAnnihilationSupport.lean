import QuantumMixedAnnihilationCoefficients
import OccupationTensorCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem occupationWeights_unit_predecessor (n l : ℕ) (x : Fin (n+1) → ℤ) (i : Fin (n+1))
    (hx : x+Pi.single i 1∈occupationWeights (Fin (n+1)) (l+1)) (hi : x i+1≠0) :
    x∈occupationWeights (Fin (n+1)) l := by
  constructor
  · intro j
    have hj:=hx.1 j
    by_cases hji : j=i
    · subst j
      simp only [Pi.add_apply,Pi.single_eq_same] at hj
      omega
    · simpa only [Pi.add_apply,Pi.single_apply,if_neg hji,add_zero] using hj
  · have hs:=hx.2
    simp only [Pi.add_apply,Finset.sum_add_distrib] at hs
    simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
    omega

theorem pairLatticeAnnihilation_apply (q : ℝ) (n : ℕ) (f : OccupationPairLattice n →₀ ℝ)
    (p : OccupationPairLattice n) :
    pairLatticeAnnihilation q n f p=
      ∑ i : Fin (n+1),f (p+mixedCreationShift n i)*mixedAnnihilationCoefficient q n i (p+mixedCreationShift n i) := by
  simp only [pairLatticeAnnihilation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply,sub_neg_eq_add]

/-- The raw annihilation retains every physical zero-occupation boundary and
lowers each finite symmetric degree by exactly one. -/
theorem pairLatticeAnnihilation_physical_support (q : ℝ) (n l m : ℕ) (f : OccupationPairLattice n →₀ ℝ)
    (hf : ∀ x y,f (x,y)≠0 → x∈occupationWeights (Fin (n+1)) (l+1) ∧ y∈occupationWeights (Fin (n+1)) (m+1))
    (x y : Fin (n+1) → ℤ) (h : pairLatticeAnnihilation q n f (x,y)≠0) :
    x∈occupationWeights (Fin (n+1)) l ∧ y∈occupationWeights (Fin (n+1)) m := by
  rw [pairLatticeAnnihilation_apply] at h
  obtain ⟨i,hi,hTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hf0 := (mul_ne_zero_iff.mp hTerm).1
  have hC := (mul_ne_zero_iff.mp hTerm).2
  have hs:=hf _ _ hf0
  change x+Pi.single i 1∈occupationWeights (Fin (n+1)) (l+1) ∧
    y+Pi.single i 1∈occupationWeights (Fin (n+1)) (m+1) at hs
  have hxq : qInteger q (x i+1)≠0 := by
    have hh := (mul_ne_zero_iff.mp ((mul_ne_zero_iff.mp hC).1)).2
    simpa only [mixedCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same] using hh
  have hyq : qInteger q (y i+1)≠0 := by
    have hh := (mul_ne_zero_iff.mp hC).2
    simpa only [mixedCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same] using hh
  have hxi : x i+1≠0 := by intro hz;exact hxq (by rw [hz,qInteger_zero])
  have hyi : y i+1≠0 := by intro hz;exact hyq (by rw [hz,qInteger_zero])
  exact ⟨occupationWeights_unit_predecessor n l x i hs.1 hxi,
    occupationWeights_unit_predecessor n m y i hs.2 hyi⟩

end AMSPhysical

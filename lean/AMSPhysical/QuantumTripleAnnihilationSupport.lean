import QuantumTripleAnnihilation
import QuantumOccupationAnnihilationSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLeftAnnihilation_apply (q : ℝ) (n : ℕ) (f : OccupationTripleLattice n →₀ ℝ) (p : OccupationTripleLattice n) :
    tripleLeftAnnihilation q n f p=∑ i : Fin (n+1),f (p+tripleLeftCreationShift n i)*
      tripleLeftAnnihilationCoefficient q n i (p+tripleLeftCreationShift n i) := by
  simp only [tripleLeftAnnihilation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply,sub_neg_eq_add]

theorem tripleRightAnnihilation_apply (q : ℝ) (n : ℕ) (f : OccupationTripleLattice n →₀ ℝ) (p : OccupationTripleLattice n) :
    tripleRightAnnihilation q n f p=∑ i : Fin (n+1),f (p+tripleRightCreationShift n i)*
      tripleRightAnnihilationCoefficient q n i (p+tripleRightCreationShift n i) := by
  simp only [tripleRightAnnihilation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply,sub_neg_eq_add]

theorem tripleLeftAnnihilation_physical_support (q : ℝ) (n l m c : ℕ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : ∀ p,f p≠0 → p.1∈occupationWeights (Fin (n+1)) (l+1) ∧
      p.2.1∈occupationWeights (Fin (n+1)) (m+1) ∧ p.2.2∈occupationWeights (Fin (n+1)) c)
    (p : OccupationTripleLattice n) (hp : tripleLeftAnnihilation q n f p≠0) :
    p.1∈occupationWeights (Fin (n+1)) l ∧ p.2.1∈occupationWeights (Fin (n+1)) m ∧
      p.2.2∈occupationWeights (Fin (n+1)) c := by
  rw [tripleLeftAnnihilation_apply] at hp
  obtain ⟨i,hi,hTerm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hp
  have hC:=(mul_ne_zero_iff.mp hTerm).2
  have hs:=hf _ (mul_ne_zero_iff.mp hTerm).1
  dsimp only [tripleLeftCreationShift,Prod.fst_add,Prod.snd_add] at hs
  simp only [add_zero] at hs
  have hx : p.1 i+1≠0 := by
    intro he
    apply hC
    simp only [tripleLeftAnnihilationCoefficient,mixedAnnihilationCoefficient,tripleLeftCreationShift,
      Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same,he,qInteger_zero,mul_zero,zero_mul]
  have hy : p.2.1 i+1≠0 := by
    intro he
    apply hC
    simp only [tripleLeftAnnihilationCoefficient,mixedAnnihilationCoefficient,tripleLeftCreationShift,
      Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same,he,qInteger_zero,mul_zero,zero_mul]
  exact ⟨occupationWeights_unit_predecessor n l p.1 i hs.1 hx,
    occupationWeights_unit_predecessor n m p.2.1 i hs.2.1 hy,hs.2.2⟩

theorem tripleRightAnnihilation_physical_support (q : ℝ) (n l m c : ℕ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : ∀ p,f p≠0 → p.1∈occupationWeights (Fin (n+1)) l ∧
      p.2.1∈occupationWeights (Fin (n+1)) (m+1) ∧ p.2.2∈occupationWeights (Fin (n+1)) (c+1))
    (p : OccupationTripleLattice n) (hp : tripleRightAnnihilation q n f p≠0) :
    p.1∈occupationWeights (Fin (n+1)) l ∧ p.2.1∈occupationWeights (Fin (n+1)) m ∧
      p.2.2∈occupationWeights (Fin (n+1)) c := by
  rw [tripleRightAnnihilation_apply] at hp
  obtain ⟨i,hi,hTerm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hp
  have hC:=(mul_ne_zero_iff.mp hTerm).2
  have hs:=hf _ (mul_ne_zero_iff.mp hTerm).1
  dsimp only [tripleRightCreationShift,Prod.fst_add,Prod.snd_add] at hs
  simp only [add_zero] at hs
  have hy : p.2.1 i+1≠0 := by
    intro he
    apply hC
    simp only [tripleRightAnnihilationCoefficient,mixedAnnihilationCoefficient,tripleRightCreationShift,
      occupationLatticeReflect,Fin.rev_rev,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same,he,
      qInteger_zero,mul_zero,zero_mul]
  have hz : p.2.2 i+1≠0 := by
    intro he
    apply hC
    simp only [tripleRightAnnihilationCoefficient,mixedAnnihilationCoefficient,tripleRightCreationShift,
      occupationLatticeReflect,Fin.rev_rev,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same,he,
      qInteger_zero,mul_zero,zero_mul]
  exact ⟨hs.1,occupationWeights_unit_predecessor n m p.2.1 i hs.2.1 hy,
    occupationWeights_unit_predecessor n c p.2.2 i hs.2.2 hz⟩

end AMSPhysical

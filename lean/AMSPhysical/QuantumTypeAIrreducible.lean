import QuantumOccupationActions
import JointSpectralSubmodule
import QuantumPositive

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem typeAInvariant_raised_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (hS : IsTypeAInvariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ)
    (hx : quantumOccupationBasis (K:=ℝ) L x∈S) :
    quantumOccupationBasis (K:=ℝ) L (raisedOccupation n L x i hi)∈S := by
  have he := typeAInvariant_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S hS i 0 _ hx
  rw [typeAFiniteGenerator_E_raised q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L x i hi] at he
  exact (S.smul_mem_iff (ne_of_gt (qInteger_pos_real q hq hq1 _ hi))).mp he

theorem typeAInvariant_reversed_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (hS : IsTypeAInvariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ)
    (hy : quantumOccupationBasis (K:=ℝ) L (raisedOccupation n L x i hi)∈S) :
    quantumOccupationBasis (K:=ℝ) L x∈S := by
  have he := typeAInvariant_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S hS i 1 _ hy
  rw [typeAFiniteGenerator_F_reversed q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L x i hi] at he
  have hpos : 0<x.val i.castSucc+1 := by have hh := x.property.1 i.castSucc;omega
  exact (S.smul_mem_iff (ne_of_gt (qInteger_pos_real q hq hq1 _ hpos))).mp he

theorem typeAInvariant_highest_of_basis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (hS : IsTypeAInvariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S)
    (x : occupationWeights (Fin (n+1)) L) (hx : quantumOccupationBasis (K:=ℝ) L x∈S) :
    quantumOccupationBasis (K:=ℝ) L (highestOccupation n L)∈S := by
  have aux : ∀ k,∀ y : occupationWeights (Fin (n+1)) L,occupationHeight n L y=k →
      quantumOccupationBasis (K:=ℝ) L y∈S → quantumOccupationBasis (K:=ℝ) L (highestOccupation n L)∈S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro y hy hymem
      by_cases he : y=highestOccupation n L
      · simpa only [he] using hymem
      · obtain ⟨i,hi⟩ := occupation_nonhighest_donor n L y he
        have hh := raisedOccupation_height n L y i hi
        exact ih (occupationHeight n L (raisedOccupation n L y i hi)) (by omega)
          (raisedOccupation n L y i hi) rfl (typeAInvariant_raised_mem q hq hq1 n L S hS y i hi hymem)
  exact aux (occupationHeight n L x) x rfl hx

/-- The actual highest vector generates the complete finite module under the
lowering generators, proved by induction on the occupation graph. -/
theorem typeAInvariant_cyclic_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (hS : IsTypeAInvariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S)
    (hhigh : quantumOccupationBasis (K:=ℝ) L (highestOccupation n L)∈S) : S=⊤ := by
  have aux : ∀ k,∀ y : occupationWeights (Fin (n+1)) L,occupationHeight n L y=k →
      quantumOccupationBasis (K:=ℝ) L y∈S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro y hy
      by_cases he : y=highestOccupation n L
      · simpa only [he] using hhigh
      · obtain ⟨i,hi⟩ := occupation_nonhighest_donor n L y he
        have hh := raisedOccupation_height n L y i hi
        have hymem := ih (occupationHeight n L (raisedOccupation n L y i hi)) (by omega)
          (raisedOccupation n L y i hi) rfl
        exact typeAInvariant_reversed_mem q hq hq1 n L S hS y i hi hymem
  apply le_antisymm le_top
  intro v hv
  rw [← (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).sum_repr v]
  apply Submodule.sum_mem
  intro x hx
  exact S.smul_mem _ (aux (occupationHeight n L x) x rfl)

/-- Genuine irreducibility of the independently constructed finite symmetric
Uq(sl_(n+1)) module, in every rank and every degree. -/
theorem typeAFiniteQuantumRepresentation_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (hS : IsTypeAInvariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S) :
    S=⊥ ∨ S=⊤ := by
  classical
  by_cases hz : S=⊥
  · exact Or.inl hz
  · right
    have hex : ∃ v∈S,v≠0 := by
      by_contra hn
      push_neg at hn
      apply hz
      apply le_antisymm _ bot_le
      intro v hv
      simpa only [Submodule.mem_bot] using hn v hv
    obtain ⟨v,hv,hv0⟩ := hex
    have hSep : ∀ x y : occupationWeights (Fin (n+1)) L,x≠y →
        ∃ i : Fin n,q^(simpleOccupationWeight n x.val i)≠q^(simpleOccupationWeight n y.val i) := by
      intro x y hxy
      by_contra hn
      push_neg at hn
      apply hxy
      apply typeA_toral_eigenvalues_injective q hq hq1 n L
      funext i
      exact hn i
    obtain ⟨x,hx⟩ := joint_diagonal_basis_mem
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
      (fun i => typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i 2)
      (fun i x => q^(simpleOccupationWeight n x.val i))
      (fun i x => typeAFiniteGenerator_K_basis q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i x)
      hSep S (fun i => typeAInvariant_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L S hS i 2)
      v hv hv0
    exact typeAInvariant_cyclic_highest q hq hq1 n L S hS
      (typeAInvariant_highest_of_basis q hq hq1 n L S hS x hx)

end AMSPhysical

#print axioms AMSPhysical.typeAFiniteQuantumRepresentation_irreducible

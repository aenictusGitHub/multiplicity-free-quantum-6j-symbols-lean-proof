import QuantumOscillatorCrossCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem finite_sum_qcommutator {A I J : Type*} [Ring A] [Module ℝ A] [Fintype I] [Fintype J]
    (L : I → A) (R : J → A) (q : ℝ) :
    (∑ i,L i)*(∑ j,R j)-q • ((∑ j,R j)*(∑ i,L i))=
      ∑ i,∑ j,(L i*R j-q • (R j*L i)) := by
  simp only [Finset.sum_mul,Finset.mul_sum,Finset.smul_sum,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

theorem mixedOscillator_component_diagonal (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (i : Fin (n+1)) :
    weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i)*
        weightedTranslation (mixedCreationShift n i) (mixedCreationCoefficient q n i)-
      q^(-2:ℤ) • (weightedTranslation (mixedCreationShift n i) (mixedCreationCoefficient q n i)*
        weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i))=
      weightedTranslation 0 (mixedRadialDiagonalCoefficient q n i) := by
  rw [weightedTranslation_qcommutator,neg_add_cancel]
  congr 1
  funext p
  simpa only [← sub_eq_add_neg] using mixedOscillator_diagonal_coefficient q hq hD n i p

theorem mixedOscillator_component_offdiagonal (q : ℝ) (hq : q≠0) (n : ℕ) (i j : Fin (n+1)) (hij : i≠j) :
    weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i)*
        weightedTranslation (mixedCreationShift n j) (mixedCreationCoefficient q n j)-
      q^(-2:ℤ) • (weightedTranslation (mixedCreationShift n j) (mixedCreationCoefficient q n j)*
        weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i))=0 := by
  rw [weightedTranslation_qcommutator]
  have hc : (fun p : OccupationPairLattice n =>
      mixedCreationCoefficient q n j p*mixedAnnihilationCoefficient q n i (p+mixedCreationShift n j)-
        q^(-2:ℤ)*mixedAnnihilationCoefficient q n i p*mixedCreationCoefficient q n j (p+ -mixedCreationShift n i))=
      (fun _ =>0) := by
    funext p
    simpa only [← sub_eq_add_neg] using mixedOscillator_offdiagonal_coefficient q hq n i j hij p
  rw [hc,weightedTranslation_zero]

/-- The exact quantum radial oscillator relation on the ACTUAL unrestricted
occupation coefficient operators, including every coordinate and boundary. -/
theorem pairLatticeAnnihilation_creation_commutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) :
    pairLatticeAnnihilation q n*pairLatticeCreation q n-
      q^(-2:ℤ) • (pairLatticeCreation q n*pairLatticeAnnihilation q n)=
      weightedTranslation 0 (fun p : OccupationPairLattice n =>
        q^(-(∑ i : Fin (n+1),p.1 i)-(∑ i : Fin (n+1),p.2 i)-(n:ℤ))*
          qInteger q ((∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2 i)+(n:ℤ)+1)) := by
  classical
  unfold pairLatticeAnnihilation pairLatticeCreation
  rw [finite_sum_qcommutator
    (fun i : Fin (n+1) =>weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i))
    (fun j : Fin (n+1) =>weightedTranslation (mixedCreationShift n j) (mixedCreationCoefficient q n j)) (q^(-2:ℤ))]
  have he : ∀ i j : Fin (n+1),
      weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i)*
          weightedTranslation (mixedCreationShift n j) (mixedCreationCoefficient q n j)-
        q^(-2:ℤ) • (weightedTranslation (mixedCreationShift n j) (mixedCreationCoefficient q n j)*
          weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i))=
      if j=i then weightedTranslation 0 (mixedRadialDiagonalCoefficient q n i) else 0 := by
    intro i j
    by_cases hij : j=i
    · subst j
      rw [if_pos rfl]
      exact mixedOscillator_component_diagonal q hq hD n i
    · rw [if_neg hij]
      exact mixedOscillator_component_offdiagonal q hq n i j (Ne.symm hij)
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [weightedTranslation_sum]
  congr 1
  funext p
  exact mixedRadialDiagonalCoefficient_sum q hq n p

end AMSPhysical
#print axioms AMSPhysical.pairLatticeAnnihilation_creation_commutator

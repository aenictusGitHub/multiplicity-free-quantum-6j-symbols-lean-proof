import QuantumTypeAChevalley
import QuantumTypeAIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

/-- The opposite-end fundamental symmetric module, built by the proved
Chevalley involution rather than by an assumed dual-module identification. -/
def typeAOppositeSymmetricRepresentation (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) :
    UqTypeA q n →ₐ[K] Module.End K (quantumOccupationSpace K (Fin (n+1)) L) :=
  (typeAFiniteQuantumRepresentation q hq hD n L).comp (typeAChevalley q hq n)

theorem typeAOpposite_generator (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) (t : Fin 4) :
    typeAOppositeSymmetricRepresentation q hq hD n L (typeAAlgebraGenerator q n i t)=
      ![typeAFiniteGenerator q hq hD n L i 1,typeAFiniteGenerator q hq hD n L i 0,
        typeAFiniteGenerator q hq hD n L i 3,typeAFiniteGenerator q hq hD n L i 2] t := by
  fin_cases t <;> simp [typeAOppositeSymmetricRepresentation,typeAChevalley_generator,typeAFiniteGenerator]

def lowestOccupation (n L : ℕ) : occupationWeights (Fin (n+1)) L :=
  ⟨Pi.single (Fin.last n) (L:ℤ),by
    constructor
    · intro k
      simp only [Pi.single_apply]
      split_ifs <;> omega
    · simp⟩

theorem lowestOccupation_source_zero (n L : ℕ) (i : Fin n) :
    (lowestOccupation n L).val i.castSucc=0 := by
  have hi : i.castSucc≠Fin.last n := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.coe_castSucc,Fin.val_last] at hh
    exact (Nat.ne_of_lt i.isLt) hh
  simp [lowestOccupation,Pi.single_apply,hi,Ne.symm hi]

theorem typeAOpposite_highest_E (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    typeAOppositeSymmetricRepresentation q hq hD n L (typeAAlgebraGenerator q n i 0)
      (quantumOccupationBasis (K:=K) L (lowestOccupation n L))=0 := by
  rw [typeAOpposite_generator]
  change typeAFiniteGenerator q hq hD n L i 1 _=0
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe,quantumOccupationBasis_coe]
  change quantumLatticeMove q i.succ i.castSucc (Finsupp.single (lowestOccupation n L).val (1:K))=0
  rw [quantumLatticeMove_single,lowestOccupation_source_zero,qInteger_zero,mul_zero,Finsupp.single_zero]

/-- The independently constructed opposite-end symmetric module is irreducible
under every element of the full presented quantum algebra. -/
theorem typeAOppositeSymmetric_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (hS : ∀ z : UqTypeA q n,∀ v∈S,typeAOppositeSymmetricRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n L z v∈S) : S=⊥ ∨ S=⊤ := by
  apply typeAFiniteQuantumRepresentation_irreducible q hq hq1 n L S
  intro z v hv
  obtain ⟨w,hw⟩ := typeAChevalley_surjective q (ne_of_gt hq) n z
  rw [← hw]
  exact hS w v hv

end AMSPhysical
#print axioms AMSPhysical.typeAOppositeSymmetric_irreducible

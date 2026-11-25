import OccupationTensorCoefficients
import QuantumTripleCreation
import InjectedBasisProperties

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

abbrev quantumOccupationTripleSpace (n l m c : ℕ) :=
  quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ]
    (quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c)

abbrev OccupationTripleIndex (n l m c : ℕ) :=
  occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m × occupationWeights (Fin (n+1)) c

def occupationTripleEmbedding (n l m c : ℕ) (p : OccupationTripleIndex n l m c) : OccupationTripleLattice n :=
  (p.1.val,p.2.1.val,p.2.2.val)

theorem occupationTripleEmbedding_injective (n l m c : ℕ) :
    Function.Injective (occupationTripleEmbedding n l m c) := by
  intro p z hz
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hz)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun w =>w.2.1) hz)
    · exact Subtype.ext (congrArg (fun w =>w.2.2) hz)

def occupationTripleBasis (n l m c : ℕ) : Module.Basis (OccupationTripleIndex n l m c) ℝ (quantumOccupationTripleSpace n l m c) :=
  (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))

def occupationTripleCoefficients (n l m c : ℕ) :
    quantumOccupationTripleSpace n l m c →ₗ[ℝ] OccupationTripleLattice n →₀ ℝ := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact injectedBasisCoefficients (V:=V) (occupationTripleBasis n l m c) (occupationTripleEmbedding n l m c)

def occupationTripleSynthesis (n l m c : ℕ) :
    (OccupationTripleLattice n →₀ ℝ) →ₗ[ℝ] quantumOccupationTripleSpace n l m c := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact injectedBasisSynthesis (V:=V) (occupationTripleBasis n l m c) (occupationTripleEmbedding n l m c)

theorem occupationTripleSynthesis_coefficients (n l m c : ℕ) (v : quantumOccupationTripleSpace n l m c) :
    occupationTripleSynthesis n l m c (occupationTripleCoefficients n l m c v)=v := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact injectedBasisSynthesis_coefficients (V:=V) (occupationTripleBasis n l m c)
    (occupationTripleEmbedding n l m c) (occupationTripleEmbedding_injective n l m c) v

theorem occupationTripleCoefficients_injective (n l m c : ℕ) : Function.Injective (occupationTripleCoefficients n l m c) := by
  intro v w he
  have hs:=congrArg (occupationTripleSynthesis n l m c) he
  simpa only [occupationTripleSynthesis_coefficients] using hs

theorem occupationTripleCoefficients_synthesis (n l m c : ℕ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : ∀ p,f p≠0 → p.1∈occupationWeights (Fin (n+1)) l ∧
      p.2.1∈occupationWeights (Fin (n+1)) m ∧ p.2.2∈occupationWeights (Fin (n+1)) c) :
    occupationTripleCoefficients n l m c (occupationTripleSynthesis n l m c f)=f := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply injectedBasisCoefficients_synthesis (V:=V) (occupationTripleBasis n l m c)
    (occupationTripleEmbedding n l m c) (occupationTripleEmbedding_injective n l m c)
  intro p hp
  have hs:=hf p hp
  exact ⟨(⟨p.1,hs.1⟩,⟨p.2.1,hs.2.1⟩,⟨p.2.2,hs.2.2⟩),rfl⟩

end AMSPhysical

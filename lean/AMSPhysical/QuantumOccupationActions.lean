import QuantumOccupationGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

/-- The actual finite E action follows an edge of the occupation graph. -/
theorem typeAFiniteGenerator_E_raised (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    typeAFiniteGenerator q hq hD n L i 0 (quantumOccupationBasis (K:=K) L x)=
      qInteger q (x.val i.succ) • quantumOccupationBasis (K:=K) L (raisedOccupation n L x i hi) := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe]
  simp only [quantumOccupationBasis_coe,Submodule.coe_smul]
  change quantumLatticeMove q i.castSucc i.succ (Finsupp.single x.val (1:K))=
    qInteger q (x.val i.succ) • Finsupp.single (raisedOccupation n L x i hi).val (1:K)
  simp only [quantumLatticeMove_single,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]
  rfl

/-- The actual finite F action reverses that edge with a nonzero source factor. -/
theorem typeAFiniteGenerator_F_reversed (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    typeAFiniteGenerator q hq hD n L i 1 (quantumOccupationBasis (K:=K) L (raisedOccupation n L x i hi))=
      qInteger q (x.val i.castSucc+1) • quantumOccupationBasis (K:=K) L x := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe]
  simp only [quantumOccupationBasis_coe,Submodule.coe_smul]
  change quantumLatticeMove q i.succ i.castSucc (Finsupp.single (raisedOccupation n L x i hi).val (1:K))=
    qInteger q (x.val i.castSucc+1) • Finsupp.single x.val (1:K)
  simp only [quantumLatticeMove_single,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]
  rw [raisedOccupation_reverse,raisedOccupation_target]

/-- Invariance means invariance under every element of the independently
presented higher-rank quantum algebra. -/
def IsTypeAInvariant (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (S : Submodule K (quantumOccupationSpace K (Fin (n+1)) L)) : Prop :=
  ∀ z : UqTypeA q n,∀ v∈S,typeAFiniteQuantumRepresentation q hq hD n L z v∈S

theorem typeAInvariant_generator (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (S : Submodule K (quantumOccupationSpace K (Fin (n+1)) L))
    (hS : IsTypeAInvariant q hq hD n L S) (i : Fin n) (t : Fin 4) :
    typeAFiniteGenerator q hq hD n L i t∈preservingEndAlgebra S :=
  hS (typeAAlgebraGenerator q n i t)

end AMSPhysical

#print axioms AMSPhysical.typeAFiniteGenerator_E_raised
#print axioms AMSPhysical.typeAFiniteGenerator_F_reversed

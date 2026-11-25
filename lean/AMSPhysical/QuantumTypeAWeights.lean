import QuantumTypeAFinite

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def typeAAlgebraGenerator (q : K) (n : ℕ) (i : Fin n) (t : Fin 4) : UqTypeA q n :=
  RingQuot.mkAlgHom K (QuantumTypeARelation q n) (typeAFreeGenerator n i t)

def typeAFiniteGenerator (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) (t : Fin 4) :
    Module.End K (quantumOccupationSpace K (Fin (n+1)) L) :=
  typeAFiniteQuantumRepresentation q hq hD n L (typeAAlgebraGenerator q n i t)

theorem typeAFiniteGenerator_coe (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (i : Fin n) (t : Fin 4) (v : quantumOccupationSpace K (Fin (n+1)) L) :
    (typeAFiniteGenerator q hq hD n L i t v).val=
      ![typeAQuantumE q n i,typeAQuantumF q n i,typeAQuantumK q n i,typeAQuantumKi q n i] t v.val :=
  typeAFiniteQuantumRepresentation_generator_coe q hq hD n L i t v

def simpleOccupationWeight (n : ℕ) (x : Fin (n+1) → ℤ) (i : Fin n) : ℤ := x i.castSucc-x i.succ

/-- At a fixed total degree the simple-root weights separate every occupation. -/
theorem simpleOccupationWeight_injective (n L : ℕ) :
    Function.Injective (fun x : occupationWeights (Fin (n+1)) L => simpleOccupationWeight n x.val) := by
  intro x y he
  have hc : ∀ k : Fin (n+1),x.val k-y.val k=x.val 0-y.val 0 := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hh := congrFun he i
      change x.val i.castSucc-x.val i.succ=y.val i.castSucc-y.val i.succ at hh
      omega
  have hs : (∑ k : Fin (n+1),(x.val k-y.val k))=0 := by
    rw [Finset.sum_sub_distrib,x.property.2,y.property.2,sub_self]
  have hsum : (∑ k : Fin (n+1),(x.val k-y.val k))=∑ _k : Fin (n+1),(x.val 0-y.val 0) :=
    Finset.sum_congr rfl (fun k _ => hc k)
  rw [hs] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hN : ((n+1:ℕ):ℤ)≠0 := by omega
  have hz : x.val 0-y.val 0=0 := (mul_eq_zero.mp hsum.symm).resolve_left hN
  apply Subtype.ext
  funext k
  have hh := hc k
  omega

theorem typeA_toral_eigenvalues_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) :
    Function.Injective (fun x : occupationWeights (Fin (n+1)) L => fun i : Fin n => q^(simpleOccupationWeight n x.val i)) := by
  intro x y he
  apply simpleOccupationWeight_injective n L
  funext i
  exact zpow_right_injective₀ hq hq1 (congrFun he i)

/-- The actual Cartan generator acts diagonally in the constructed occupation basis. -/
theorem typeAFiniteGenerator_K_basis (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) L) :
    typeAFiniteGenerator q hq hD n L i 2 (quantumOccupationBasis (K:=K) L x)=
      q^(simpleOccupationWeight n x.val i) • quantumOccupationBasis (K:=K) L x := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe,quantumOccupationBasis_coe]
  change quantumLatticeCartan q (typeARoot n i) (Finsupp.single x.val (1:K))=_
  simp only [quantumLatticeCartan_single,typeARoot,latticePairing_root_left,one_mul,
    Submodule.coe_smul,quantumOccupationBasis_coe,Finsupp.smul_single,smul_eq_mul,mul_one,simpleOccupationWeight]

def highestOccupation (n L : ℕ) : occupationWeights (Fin (n+1)) L :=
  ⟨Pi.single 0 (L:ℤ),by
    constructor
    · intro k
      simp only [Pi.single_apply]
      split_ifs <;> omega
    · simp⟩

theorem highestOccupation_source_zero (n L : ℕ) (i : Fin n) :
    (highestOccupation n L).val i.succ=0 := by
  have hi : i.succ≠(0:Fin (n+1)) := by intro h;have hh := congrArg Fin.val h;simp only [Fin.val_succ,Fin.val_zero] at hh;omega
  simp [highestOccupation,Pi.single_apply,hi,Ne.symm hi]

theorem typeAFiniteGenerator_highest_E (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) (i : Fin n) :
    typeAFiniteGenerator q hq hD n L i 0 (quantumOccupationBasis (K:=K) L (highestOccupation n L))=0 := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe,quantumOccupationBasis_coe]
  change quantumLatticeMove q i.castSucc i.succ (Finsupp.single (highestOccupation n L).val (1:K))=0
  rw [quantumLatticeMove_single,highestOccupation_source_zero,qInteger_zero,mul_zero,Finsupp.single_zero]

end AMSPhysical

#print axioms AMSPhysical.typeA_toral_eigenvalues_injective
#print axioms AMSPhysical.typeAFiniteGenerator_highest_E

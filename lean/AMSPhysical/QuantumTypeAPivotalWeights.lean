import QuantumOccupationCharacter
import QuantumTypeAWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeAPivotalExponent (n : ℕ) (i : Fin n) : ℕ := (i.val+1)*(n-i.val)

theorem typeAPivotalExponent_cast (n : ℕ) (i : Fin n) :
    (typeAPivotalExponent n i : ℤ)=((i.val:ℤ)+1)*((n:ℤ)-i.val) := by
  unfold typeAPivotalExponent
  rw [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (Nat.le_of_lt i.isLt)]

theorem typeAPivotalWeight_pairing (n : ℕ) (x : Fin (n+1) → ℤ) :
    (∑ i : Fin n,(typeAPivotalExponent n i : ℤ)*(x i.succ-x i.castSucc))=
      latticePairing (typeAInversePivotalWeight n) x := by
  let f : Fin (n+1) → ℤ := fun k => (k.val:ℤ)*((n:ℤ)+1-k.val)
  let g : Fin (n+1) → ℤ := fun k => ((k.val:ℤ)+1)*((n:ℤ)-k.val)
  have hf : (∑ i : Fin n,f i.succ*x i.succ)=∑ k : Fin (n+1),f k*x k := by
    rw [Fin.sum_univ_succ]
    simp [f]
  have hg : (∑ i : Fin n,g i.castSucc*x i.castSucc)=∑ k : Fin (n+1),g k*x k := by
    rw [Fin.sum_univ_castSucc]
    simp [g]
  calc
    _ = (∑ i : Fin n,f i.succ*x i.succ)-(∑ i : Fin n,g i.castSucc*x i.castSucc) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [typeAPivotalExponent_cast]
      dsimp [f,g]
      ring
    _ = (∑ k : Fin (n+1),f k*x k)-(∑ k : Fin (n+1),g k*x k) := by rw [hf,hg]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f,g,typeAInversePivotalWeight]
      ring

variable {K : Type*} [Field K]

theorem typeAFiniteGenerator_Ki_basis (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) L) :
    typeAFiniteGenerator q hq hD n L i 3 (quantumOccupationBasis (K:=K) L x)=
      q^(-simpleOccupationWeight n x.val i) • quantumOccupationBasis (K:=K) L x := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe,quantumOccupationBasis_coe]
  change quantumLatticeCartan q (-typeARoot n i) (Finsupp.single x.val (1:K))=_
  have hneg : latticePairing (-latticeRoot i.castSucc i.succ) x.val= -latticePairing (latticeRoot i.castSucc i.succ) x.val := by
    simp only [latticePairing,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
  simp only [quantumLatticeCartan_single,hneg,typeARoot,latticePairing_root_left,
    one_mul,Submodule.coe_smul,quantumOccupationBasis_coe,Finsupp.smul_single,smul_eq_mul,mul_one,
    simpleOccupationWeight]

end AMSPhysical
#print axioms AMSPhysical.typeAPivotalWeight_pairing

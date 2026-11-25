import QuantumOccupationActions

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

def loweredOccupation (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) (i : Fin n)
    (hi : 0<x.val i.castSucc) : occupationWeights (Fin (n+1)) L :=
  ⟨x.val+latticeRoot i.succ i.castSucc,
    occupationWeights_move L x.val x.property i.succ i.castSucc (Ne.symm (typeA_root_endpoints n i)) (ne_of_gt hi)⟩

theorem loweredOccupation_source_positive (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.castSucc) : 0<(loweredOccupation n L x i hi).val i.succ := by
  change 0<(x.val+latticeRoot i.succ i.castSucc) i.succ
  rw [Pi.add_apply,latticeRoot_target _ _ (Ne.symm (typeA_root_endpoints n i))]
  have hnonneg := x.property.1 i.succ
  omega

theorem raised_loweredOccupation (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.castSucc) :
    raisedOccupation n L (loweredOccupation n L x i hi) i (loweredOccupation_source_positive n L x i hi)=x := by
  apply Subtype.ext
  change x.val+latticeRoot i.succ i.castSucc+latticeRoot i.castSucc i.succ=x.val
  rw [latticeRoot_swap i.succ i.castSucc]
  abel

theorem raisedOccupation_injective (n L : ℕ) (i : Fin n)
    (x y : occupationWeights (Fin (n+1)) L) (hx : 0<x.val i.succ) (hy : 0<y.val i.succ)
    (he : raisedOccupation n L x i hx=raisedOccupation n L y i hy) : x=y := by
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  change x.val+latticeRoot i.castSucc i.succ=y.val+latticeRoot i.castSucc i.succ at hh
  exact add_right_cancel hh

theorem typeAFiniteGenerator_E_zero (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : x.val i.succ=0) :
    typeAFiniteGenerator q hq hD n L i 0 (quantumOccupationBasis (K:=K) L x)=0 := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe,quantumOccupationBasis_coe]
  change quantumLatticeMove q i.castSucc i.succ (Finsupp.single x.val (1:K))=0
  rw [quantumLatticeMove_single,hi,qInteger_zero,mul_zero,Finsupp.single_zero]

theorem typeAFiniteGenerator_F_zero (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : x.val i.castSucc=0) :
    typeAFiniteGenerator q hq hD n L i 1 (quantumOccupationBasis (K:=K) L x)=0 := by
  apply Subtype.ext
  rw [typeAFiniteGenerator_coe,quantumOccupationBasis_coe]
  change quantumLatticeMove q i.succ i.castSucc (Finsupp.single x.val (1:K))=0
  rw [quantumLatticeMove_single,hi,qInteger_zero,mul_zero,Finsupp.single_zero]

end AMSPhysical
#print axioms AMSPhysical.raised_loweredOccupation

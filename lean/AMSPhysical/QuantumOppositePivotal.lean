import QuantumTypeAPivotEigen
import QuantumReflectionCartan
import QuantumTypeADualSymmetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem latticePairing_neg_left_typeA (n : ℕ) (h x : Fin (n+1) → ℤ) :
    latticePairing (-h) x= -latticePairing h x := by
  simp only [latticePairing,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]

theorem typeAInversePivotalWeight_reflect (n : ℕ) :
    occupationLatticeReflect n (typeAInversePivotalWeight n)= -typeAInversePivotalWeight n := by
  funext k
  have hk:=k.isLt
  simp only [occupationLatticeReflect,typeAInversePivotalWeight,Pi.neg_apply,Fin.val_rev]
  omega

theorem typeAInversePivotal_pairing_reflect (n : ℕ) (x : Fin (n+1) → ℤ) :
    latticePairing (typeAInversePivotalWeight n) (occupationLatticeReflect n x)=
      latticePairing (-typeAInversePivotalWeight n) x := by
  have h:=occupationLatticeReflect_pairing n (typeAInversePivotalWeight n) (occupationLatticeReflect n x)
  have hi : occupationLatticeReflect n (occupationLatticeReflect n x)=x := by
    funext k
    exact congrArg x (Fin.rev_rev k)
  rw [typeAInversePivotalWeight_reflect,hi] at h
  exact h.symm

theorem typeAOpposite_inversePivot_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) :
    typeAOppositeSymmetricRepresentation q hq hD n L (typeAInversePivot q n)
      (quantumOccupationBasis (K:=ℝ) L x)=
      q^(latticePairing (-typeAInversePivotalWeight n) x.val) • quantumOccupationBasis (K:=ℝ) L x := by
  have h:=typeAInversePivot_eigen q hq n (typeAOppositeSymmetricRepresentation q hq hD n L)
    (quantumOccupationBasis (K:=ℝ) L x) (simpleOccupationWeight n x.val) (fun i =>by
      rw [typeAOpposite_generator]
      exact typeAFiniteGenerator_K_basis q hq hD n L i x)
  rw [latticePairing_neg_left_typeA]
  have he : (∑ i : Fin n,(typeAPivotalExponent n i : ℤ)*simpleOccupationWeight n x.val i)=
      -latticePairing (typeAInversePivotalWeight n) x.val := by
    rw [← typeAPivotalWeight_pairing]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold simpleOccupationWeight
    ring
  rw [he] at h
  exact h

theorem typeAOpposite_inversePivot_representation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) :
    typeAOppositeSymmetricRepresentation q hq hD n L (typeAInversePivot q n)=
      finiteOccupationCartan q L (-typeAInversePivotalWeight n) := by
  apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
  intro x
  rw [typeAOpposite_inversePivot_basis,finiteOccupationCartan_basis]

theorem typeAOpposite_pivotal_dimension (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0) (n L : ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L)
      (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) hD n L (typeAInversePivot q n))=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) := by
  rw [typeAOpposite_inversePivot_representation,finiteOccupationCartan_trace]
  calc
    _ = ∑ x : occupationWeights (Fin (n+1)) L,
        q^(latticePairing (typeAInversePivotalWeight n) (occupationReflection n L x).val) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact congrArg (fun z : ℤ =>q^z) (typeAInversePivotal_pairing_reflect n x.val).symm
    _ = ∑ x : occupationWeights (Fin (n+1)) L,q^(latticePairing (typeAInversePivotalWeight n) x.val) :=
      Equiv.sum_comp (occupationReflectionEquiv n L)
        (fun x : occupationWeights (Fin (n+1)) L =>q^(latticePairing (typeAInversePivotalWeight n) x.val))
    _ = _ := by rw [← finiteOccupationCartan_trace,inversePivotal_trace_factorial q hq]

end AMSPhysical
#print axioms AMSPhysical.typeAOpposite_pivotal_dimension

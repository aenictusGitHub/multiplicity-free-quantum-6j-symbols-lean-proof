import QuantumLattice

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {K ι : Type*} [Field K] [DecidableEq ι]

theorem quantumLatticeMove_same_source (q : K) (i j k : ι) (hij : i≠j) (hkj : k≠j) :
    quantumLatticeMove q i j*quantumLatticeMove q k j=
      quantumLatticeMove q k j*quantumLatticeMove q i j := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [Module.End.mul_apply,quantumLatticeMove_single,Pi.add_apply,
    latticeRoot_source k j hkj,latticeRoot_source i j hij]
  have he : x+latticeRoot k j+latticeRoot i j=x+latticeRoot i j+latticeRoot k j := by abel
  rw [he]

theorem quantumLatticeMove_commute (q : K) (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hli : l≠i) :
    quantumLatticeMove q i j*quantumLatticeMove q k l=
      quantumLatticeMove q k l*quantumLatticeMove q i j := by
  by_cases hjl : j=l
  · subst l
    exact quantumLatticeMove_same_source q i j k hij hkl
  · apply Finsupp.lhom_ext
    intro x a
    simp only [Module.End.mul_apply,quantumLatticeMove_single,Pi.add_apply,
      latticeRoot_other k l j hjk hjl,latticeRoot_other i j l hli (Ne.symm hjl),add_zero]
    have he : x+latticeRoot k l+latticeRoot i j=x+latticeRoot i j+latticeRoot k l := by abel
    rw [he]
    congr 1
    ring

section RootPair
variable [Fintype ι]

/-- The defining E/F commutator holds in every root direction, in arbitrary
rank, on the independently defined occupation-space representation. -/
theorem quantumLatticeMove_commutator (q : K) (hq : q≠0) (hD : q-q⁻¹≠0)
    (i j : ι) (hij : i≠j) :
    quantumLatticeMove q i j*quantumLatticeMove q j i-
      quantumLatticeMove q j i*quantumLatticeMove q i j=
      (q-q⁻¹)⁻¹ • (quantumLatticeCartan q (latticeRoot i j)-quantumLatticeCartan q (-latticeRoot i j)) := by
  apply Finsupp.lhom_ext
  intro x a
  have hidx₁ : x+latticeRoot j i+latticeRoot i j=x := by rw [latticeRoot_swap];abel
  have hidx₂ : x+latticeRoot i j+latticeRoot j i=x := by rw [latticeRoot_swap];abel
  have hpair : latticePairing (-latticeRoot i j) x= -(x i-x j) := by
    simp only [latticePairing,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
    change -latticePairing (latticeRoot i j) x= -(x i-x j)
    rw [latticePairing_root_left]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,quantumLatticeMove_single,
    quantumLatticeCartan_single,LinearMap.smul_apply,Pi.add_apply,
    latticeRoot_target j i (Ne.symm hij),latticeRoot_target i j hij,
    hidx₁,hidx₂,latticePairing_root_left,hpair,← Finsupp.single_sub,Finsupp.smul_single,smul_eq_mul]
  apply congrArg (Finsupp.single x)
  have hc := qInteger_cross q hq hD (x j) (x i)
  calc
    (a*qInteger q (x i))*qInteger q (x j+1)-(a*qInteger q (x j))*qInteger q (x i+1)=
      a*(qInteger q (x j+1)*qInteger q (x i)-qInteger q (x j)*qInteger q (x i+1)) := by ring
    _ = a*qInteger q (x i-x j) := by rw [hc]
    _ = _ := by unfold qInteger;ring

end RootPair
end AMSPhysical

#print axioms AMSPhysical.quantumLatticeMove_commutator
#print axioms AMSPhysical.quantumLatticeMove_commute

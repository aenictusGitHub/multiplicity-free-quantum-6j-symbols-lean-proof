import QuantumOccupationReflection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def occupationLatticeReflect (n : ℕ) (x : Fin (n+1) → ℤ) : Fin (n+1) → ℤ := fun k =>x k.rev

def quantumLatticeReflection (n : ℕ) : Module.End ℝ (QuantumLatticeSpace ℝ (Fin (n+1))) :=
  Finsupp.lmapDomain ℝ ℝ (occupationLatticeReflect n)

@[simp] theorem quantumLatticeReflection_single (n : ℕ) (x : Fin (n+1) → ℤ) (a : ℝ) :
    quantumLatticeReflection n (Finsupp.single x a)=Finsupp.single (occupationLatticeReflect n x) a :=
  Finsupp.mapDomain_single

theorem occupationLatticeReflect_root (n : ℕ) (a b : Fin (n+1)) :
    occupationLatticeReflect n (latticeRoot a b)=latticeRoot a.rev b.rev := by
  funext k
  simp only [occupationLatticeReflect,latticeRoot,Pi.sub_apply,Pi.single_apply]
  simp only [Fin.rev_eq_iff,Fin.rev_rev]

theorem occupationLatticeReflect_add (n : ℕ) (x y : Fin (n+1) → ℤ) :
    occupationLatticeReflect n (x+y)=occupationLatticeReflect n x+occupationLatticeReflect n y := rfl

theorem quantumLatticeReflection_move (q : ℝ) (n : ℕ) (a b : Fin (n+1))
    (v : QuantumLatticeSpace ℝ (Fin (n+1))) :
    quantumLatticeReflection n (quantumLatticeMove q a b v)=
      quantumLatticeMove q a.rev b.rev (quantumLatticeReflection n v) := by
  have he : (quantumLatticeReflection n).comp (quantumLatticeMove q a b)=
      (quantumLatticeMove q a.rev b.rev).comp (quantumLatticeReflection n) := by
    apply Finsupp.lhom_ext
    intro x c
    simp only [LinearMap.comp_apply,quantumLatticeMove_single,quantumLatticeReflection_single,
      occupationLatticeReflect_add,occupationLatticeReflect_root,occupationLatticeReflect,Fin.rev_rev]
  exact DFunLike.congr_fun he v

theorem occupationLatticeReflect_simple_weight (n : ℕ) (i : Fin n) (x : Fin (n+1) → ℤ) :
    simpleOccupationWeight n (occupationLatticeReflect n x) i.rev= -simpleOccupationWeight n x i := by
  simp only [simpleOccupationWeight,occupationLatticeReflect,Fin.rev_castSucc,Fin.rev_succ,Fin.rev_rev]
  ring

theorem quantumLatticeReflection_typeA_E (q : ℝ) (n : ℕ) (i : Fin n)
    (v : QuantumLatticeSpace ℝ (Fin (n+1))) :
    quantumLatticeReflection n (typeAQuantumE q n i v)=typeAQuantumF q n i.rev (quantumLatticeReflection n v) := by
  change quantumLatticeReflection n (quantumLatticeMove q i.castSucc i.succ v)=_
  rw [quantumLatticeReflection_move]
  simp only [Fin.rev_castSucc,Fin.rev_succ]
  rfl

theorem quantumLatticeReflection_typeA_F (q : ℝ) (n : ℕ) (i : Fin n)
    (v : QuantumLatticeSpace ℝ (Fin (n+1))) :
    quantumLatticeReflection n (typeAQuantumF q n i v)=typeAQuantumE q n i.rev (quantumLatticeReflection n v) := by
  change quantumLatticeReflection n (quantumLatticeMove q i.succ i.castSucc v)=_
  rw [quantumLatticeReflection_move]
  simp only [Fin.rev_castSucc,Fin.rev_succ]
  rfl

theorem quantumOccupationReflection_coe (n L : ℕ) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    (quantumOccupationReflection n L v).val=quantumLatticeReflection n v.val := by
  have he : (quantumOccupationSpace ℝ (Fin (n+1)) L).subtype.comp (quantumOccupationReflection n L).toLinearMap=
      (quantumLatticeReflection n).comp (quantumOccupationSpace ℝ (Fin (n+1)) L).subtype := by
    apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
    intro x
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply,
      quantumOccupationReflection_basis,quantumOccupationBasis_coe,quantumLatticeReflection_single]
    rfl
  exact DFunLike.congr_fun he v

end AMSPhysical

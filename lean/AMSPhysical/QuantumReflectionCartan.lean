import QuantumLatticeReflection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem occupationLatticeReflect_pairing (n : ℕ) (h x : Fin (n+1) → ℤ) :
    latticePairing (occupationLatticeReflect n h) (occupationLatticeReflect n x)=latticePairing h x :=
  Equiv.sum_comp Fin.revPerm (fun k =>h k*x k)

theorem occupationLatticeReflect_typeARoot (n : ℕ) (i : Fin n) :
    occupationLatticeReflect n (typeARoot n i)= -typeARoot n i.rev := by
  rw [typeARoot,occupationLatticeReflect_root,Fin.rev_castSucc,Fin.rev_succ]
  exact latticeRoot_swap _ _

theorem occupationLatticeReflect_neg (n : ℕ) (h : Fin (n+1) → ℤ) :
    occupationLatticeReflect n (-h)= -occupationLatticeReflect n h := rfl

theorem quantumLatticeReflection_cartan (q : ℝ) (n : ℕ) (h : Fin (n+1) → ℤ)
    (v : QuantumLatticeSpace ℝ (Fin (n+1))) :
    quantumLatticeReflection n (quantumLatticeCartan q h v)=
      quantumLatticeCartan q (occupationLatticeReflect n h) (quantumLatticeReflection n v) := by
  have he : (quantumLatticeReflection n).comp (quantumLatticeCartan q h)=
      (quantumLatticeCartan q (occupationLatticeReflect n h)).comp (quantumLatticeReflection n) := by
    apply Finsupp.lhom_ext
    intro x c
    simp only [LinearMap.comp_apply,quantumLatticeCartan_single,quantumLatticeReflection_single,
      occupationLatticeReflect_pairing]
  exact DFunLike.congr_fun he v

theorem quantumLatticeReflection_typeA_K (q : ℝ) (n : ℕ) (i : Fin n)
    (v : QuantumLatticeSpace ℝ (Fin (n+1))) :
    quantumLatticeReflection n (typeAQuantumK q n i v)=typeAQuantumKi q n i.rev (quantumLatticeReflection n v) := by
  change quantumLatticeReflection n (quantumLatticeCartan q (typeARoot n i) v)=_
  rw [quantumLatticeReflection_cartan,occupationLatticeReflect_typeARoot]
  rfl

theorem quantumLatticeReflection_typeA_Ki (q : ℝ) (n : ℕ) (i : Fin n)
    (v : QuantumLatticeSpace ℝ (Fin (n+1))) :
    quantumLatticeReflection n (typeAQuantumKi q n i v)=typeAQuantumK q n i.rev (quantumLatticeReflection n v) := by
  change quantumLatticeReflection n (quantumLatticeCartan q (-typeARoot n i) v)=_
  rw [quantumLatticeReflection_cartan,occupationLatticeReflect_neg,occupationLatticeReflect_typeARoot,neg_neg]
  rfl

end AMSPhysical

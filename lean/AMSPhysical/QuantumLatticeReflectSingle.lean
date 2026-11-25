import QuantumLatticeReflection

set_option autoImplicit false
noncomputable section
namespace AMSPhysical

theorem occupationLatticeReflect_single (n : ℕ) (i : Fin (n+1)) :
    occupationLatticeReflect n (Pi.single i 1)=Pi.single i.rev 1 := by
  funext k
  simp only [occupationLatticeReflect,Pi.single_apply,Fin.rev_eq_iff]

end AMSPhysical

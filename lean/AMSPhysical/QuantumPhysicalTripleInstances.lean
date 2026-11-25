import OccupationTripleCoefficients

set_option autoImplicit false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

instance quantumPhysicalPairAddCommGroup (n l m : ℕ) :
    AddCommGroup (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  TensorProduct.addCommGroup

instance quantumPhysicalTripleAddCommGroup (n l m c : ℕ) :
    AddCommGroup (quantumOccupationTripleSpace n l m c) := TensorProduct.addCommGroup

end AMSPhysical

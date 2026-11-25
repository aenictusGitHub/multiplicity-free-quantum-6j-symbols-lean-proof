import QuantumTripleMetric
import QuantumAssociatorIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def finiteTripleRepresentation (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0) (l m n : ℕ) :
    UqSL2 q →ₐ[ℝ] Module.End ℝ
      ((finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n) :=
  tensorRepresentation
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) (W:=finiteWeightSpace (K:=ℝ) n)
    q hq (finiteTensorRepresentation q hq hd l m) (finiteQuantumRepresentation q hq hd n)

def finiteRightTripleRepresentation (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0) (l m n : ℕ) :
    UqSL2 q →ₐ[ℝ] Module.End ℝ
      (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)) :=
  tensorRepresentation
    (V:=finiteWeightSpace (K:=ℝ) l) (W:=finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)
    q hq (finiteQuantumRepresentation q hq hd l) (finiteTensorRepresentation q hq hd m n)

theorem finiteTripleRepresentation_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    IsCompactQuantumPair
      (V:=(finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)
      q (quantumTripleBilin q l m n)
      (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n) := by
  exact compactQuantumPair_tensor
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) (W:=finiteWeightSpace (K:=ℝ) n)
    q (ne_of_gt hq)
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m))
    (standardWeightBasis (K:=ℝ) n)
    (fun ij : Fin (l+1) × Fin (m+1) => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val)
    (fun k => quantumWeight q n k.val)
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
    (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n)
    (finiteQuantumTensor_compact q hq hq1 l m) (finiteQuantum_compact q hq hq1 n)

theorem finiteTripleRepresentation_assoc (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0) (l m n : ℕ) :
    IsQuantumIntertwiner
      (V:=(finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)
      (W:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)) q
      (finiteTripleRepresentation q hq hd l m n) (finiteRightTripleRepresentation q hq hd l m n)
      (TensorProduct.assoc ℝ _ _ _).toLinearMap :=
  quantumAssociator_intertwines
    (V:=finiteWeightSpace (K:=ℝ) l) (W:=finiteWeightSpace (K:=ℝ) m) (U:=finiteWeightSpace (K:=ℝ) n)
    q hq (finiteQuantumRepresentation q hq hd l) (finiteQuantumRepresentation q hq hd m)
      (finiteQuantumRepresentation q hq hd n)

end AMSPhysical

#print axioms AMSPhysical.finiteTripleRepresentation_compact

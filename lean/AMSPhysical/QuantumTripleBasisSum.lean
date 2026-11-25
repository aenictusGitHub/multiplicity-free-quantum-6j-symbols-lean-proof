import QuantumRecouplingConstruction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

theorem quantumTripleBilin_basis_sum (q:ℝ) (l m n:ℕ) (v w:RealQuantumTripleSpace l m n):
    quantumTripleBilin q l m n v w=
      ∑ i:Fin (l+1),∑ j:Fin (m+1),∑ k:Fin (n+1),
        quantumWeight q l i.val*quantumWeight q m j.val*quantumWeight q n k.val*
          (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
            (standardWeightBasis (K:=ℝ) n)).repr v ((i,j),k)*
          (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
            (standardWeightBasis (K:=ℝ) n)).repr w ((i,j),k) := by
  change (∑ ijk:(Fin (l+1) × Fin (m+1)) × Fin (n+1),
    (quantumWeight q l ijk.1.1.val*quantumWeight q m ijk.1.2.val)*quantumWeight q n ijk.2.val*
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
        (standardWeightBasis (K:=ℝ) n)).repr v ijk*
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
        (standardWeightBasis (K:=ℝ) n)).repr w ijk)=_
  simp only [Fintype.sum_prod_type]

end AMSPhysical
#print axioms AMSPhysical.quantumTripleBilin_basis_sum

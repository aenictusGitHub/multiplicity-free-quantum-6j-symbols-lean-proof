import QuantumProjectedCoordinates
import FiniteTensorCoefficient
import TensorAssociatorCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem quantumLeftTreeHighest_basis_coefficient (q:ℝ) (hq:0<q) (hq1:q≠1) (l m n:ℕ)
    (p:LeftHighestPath l m n) (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
      (standardWeightBasis (K:=ℝ) n)).repr
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2) ((i,j),k)=
      (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) n p.2))⁻¹*
        ∑ t:Fin (p.2.val+1),couplingCoefficient q (n:ℤ) p.2.val t.val*
          standardClebschCoefficient q hq hq1 l m p.1 (leftRootIndexPair l m n p t).1 i.val j.val*
          (if (leftRootIndexPair l m n p t).2=k then 1 else 0) := by
  classical
  rw [quantumLeftTreeHighest_decomposition]
  simp only [map_smul,map_sum,Finsupp.smul_apply,Finsupp.finset_sum_apply,smul_eq_mul,
    Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,Finsupp.single_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [standardClebschCoefficient_eq_repr]
  ring

def rightRootIndexPair (l m n:ℕ) (p:RightHighestPath l m n) (t:Fin (p.2.val+1)):
    Fin (l+1) × Fin (coupledLabel m n p.1+1):=
  couplingBasisIndex l (coupledLabel m n p.1) p.2.val
    (channel_left_bound l (coupledLabel m n p.1) p.2)
    (channel_right_bound l (coupledLabel m n p.1) p.2) t

theorem quantumRightTreeHighest_assoc_decomposition (q:ℝ) (hq:0<q) (hq1:q≠1) (l m n:ℕ)
    (p:RightHighestPath l m n):
    (TensorProduct.assoc ℝ _ _ _) (quantumRightTreeHighest q hq hq1 l m n p.1 p.2)=
      (Real.sqrt (quantumHighestNorm q l (coupledLabel m n p.1) p.2))⁻¹ •
        ∑ t:Fin (p.2.val+1),couplingCoefficient q (coupledLabel m n p.1:ℤ) p.2.val t.val •
          (standardWeightBasis l (rightRootIndexPair l m n p t).1 ⊗ₜ[ℝ]
            unitaryQuantumClebschMap q hq hq1 m n p.1
              (standardWeightBasis (coupledLabel m n p.1) (rightRootIndexPair l m n p t).2)) := by
  unfold quantumRightTreeHighest quantumRightTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  change TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n p.1)
    ((Real.sqrt (quantumHighestNorm q l (coupledLabel m n p.1) p.2))⁻¹ •
      quantumClebschMap q hq hq1 l (coupledLabel m n p.1) p.2
        (standardWeightBasis (coupledLabel l (coupledLabel m n p.1) p.2) 0))=_
  rw [quantumClebschMap_highest,map_smul,finiteCoupledHighest_basis,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [map_smul,Module.Basis.tensorProduct_apply',TensorProduct.map_tmul,Module.End.one_apply]
  rfl

theorem quantumRightTreeHighest_basis_coefficient (q:ℝ) (hq:0<q) (hq1:q≠1) (l m n:ℕ)
    (p:RightHighestPath l m n) (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
      (standardWeightBasis (K:=ℝ) n)).repr
      (quantumRightTreeHighest q hq hq1 l m n p.1 p.2) ((i,j),k)=
      (Real.sqrt (quantumHighestNorm q l (coupledLabel m n p.1) p.2))⁻¹*
        ∑ t:Fin (p.2.val+1),couplingCoefficient q (coupledLabel m n p.1:ℤ) p.2.val t.val*
          (if (rightRootIndexPair l m n p t).1=i then 1 else 0)*
          standardClebschCoefficient q hq hq1 m n p.1 (rightRootIndexPair l m n p t).2 j.val k.val := by
  classical
  rw [← tensor_assoc_coordinate,quantumRightTreeHighest_assoc_decomposition]
  simp only [map_smul,map_sum,Finsupp.smul_apply,Finsupp.finset_sum_apply,smul_eq_mul,
    Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,Finsupp.single_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [standardClebschCoefficient_eq_repr]
  ring

end AMSPhysical
#print axioms AMSPhysical.quantumLeftTreeHighest_basis_coefficient
#print axioms AMSPhysical.quantumRightTreeHighest_basis_coefficient

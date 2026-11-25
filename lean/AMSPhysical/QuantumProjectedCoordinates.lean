import QuantumProjectedRecoupling
import QuantumClebschFirstZero

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem tensorCoefficient_tmul (k j : ℤ) (p v : WeightModule ℝ) :
    tensorCoefficient k j (p ⊗ₜ[ℝ] v)=p k*v j := by
  simp [tensorCoefficient]

def finiteTensorCoefficient (l m : ℕ) (k j : ℤ) : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m →ₗ[ℝ] ℝ :=
  (tensorCoefficient k j).comp (finiteTensorForget l m)

theorem finiteTensorCoefficient_tmul (l m : ℕ) (k j : ℤ) (p : RealQuantumSpace l) (v : RealQuantumSpace m) :
    finiteTensorCoefficient l m k j (p ⊗ₜ[ℝ] v)=p.val k*v.val j := by
  simp only [finiteTensorCoefficient,LinearMap.comp_apply,finiteTensorForget,TensorProduct.map_tmul,
    Submodule.subtype_apply,tensorCoefficient_tmul]

theorem firstTripleProjection_coefficient_tmul (l m n : ℕ) (y z : ℤ)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) (v : RealQuantumSpace n) :
    finiteTensorCoefficient m n y z (firstTripleProjection l m n (p ⊗ₜ[ℝ] v))=
      finiteTensorCoefficient l m 0 y p*v.val z := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul,map_zero,zero_mul]
  | tmul a b =>
    unfold firstTripleProjection
    rw [LinearMap.comp_apply,LinearEquiv.coe_coe,TensorProduct.assoc_tmul,
      tensorFirstProjection_tmul,map_smul,smul_eq_mul,finiteTensorCoefficient_tmul,finiteTensorCoefficient_tmul]
    change a.val 0*(b.val y*v.val z)=(a.val 0*b.val y)*v.val z
    ring
  | add a b ha hb =>
    rw [TensorProduct.add_tmul,map_add,map_add,ha,hb,map_add,add_mul]

theorem standardWeightBasis_forget_eval (L : ℕ) (k : Fin (L+1)) (z : ℤ) :
    (standardWeightBasis (K:=ℝ) L k).val z=if (k.val:ℤ)=z then 1 else 0 := by
  rw [standardWeightBasis_apply]
  change Finsupp.single (k.val:ℤ) (1:ℝ) z=_
  exact Finsupp.single_apply

def leftRootIndexPair (l m n : ℕ) (p : LeftHighestPath l m n) (k : Fin (p.2.val+1)) :
    Fin (coupledLabel l m p.1+1) × Fin (n+1) :=
  couplingBasisIndex (coupledLabel l m p.1) n p.2.val
    (channel_left_bound (coupledLabel l m p.1) n p.2)
    (channel_right_bound (coupledLabel l m p.1) n p.2) k

theorem quantumLeftTreeHighest_decomposition (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    quantumLeftTreeHighest q hq hq1 l m n p.1 p.2=
      (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) n p.2))⁻¹ •
        ∑ k : Fin (p.2.val+1),couplingCoefficient q (n:ℤ) p.2.val k.val •
          ((unitaryQuantumClebschMap q hq hq1 l m p.1
            (standardWeightBasis (coupledLabel l m p.1) (leftRootIndexPair l m n p k).1)) ⊗ₜ[ℝ]
            standardWeightBasis n (leftRootIndexPair l m n p k).2) := by
  unfold quantumLeftTreeHighest quantumLeftTreeMap
  rw [LinearMap.comp_apply]
  change TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m p.1) 1
    ((Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) n p.2))⁻¹ •
      quantumClebschMap q hq hq1 (coupledLabel l m p.1) n p.2
        (standardWeightBasis (coupledLabel (coupledLabel l m p.1) n p.2) 0))=_
  rw [quantumClebschMap_highest,map_smul,finiteCoupledHighest_basis,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul,Basis.tensorProduct_apply',TensorProduct.map_tmul,Module.End.one_apply]
  rfl

theorem quantumLeftTreeHighest_coefficient (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (y z : ℤ) :
    finiteTensorCoefficient m n y z (firstTripleProjection l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2))=
      (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) n p.2))⁻¹*
        ∑ k : Fin (p.2.val+1),couplingCoefficient q (n:ℤ) p.2.val k.val*
          standardClebschCoefficient q hq hq1 l m p.1 (leftRootIndexPair l m n p k).1 0 y*
          (if (((leftRootIndexPair l m n p k).2.val):ℤ)=z then 1 else 0) := by
  rw [quantumLeftTreeHighest_decomposition]
  simp only [map_smul,map_sum,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [firstTripleProjection_coefficient_tmul,standardWeightBasis_forget_eval]
  simp only [finiteTensorCoefficient,LinearMap.comp_apply,standardClebschCoefficient]
  ring

end AMSPhysical

#print axioms AMSPhysical.quantumLeftTreeHighest_coefficient

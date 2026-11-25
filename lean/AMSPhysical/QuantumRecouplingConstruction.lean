import QuantumTripleMetric
import QuantumClebschIsometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

abbrev RealQuantumSpace (L : ℕ) := finiteWeightSpace (K:=ℝ) L
abbrev RealQuantumTripleSpace (l m n : ℕ) := (RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) ⊗[ℝ] RealQuantumSpace n

def quantumLeftTreeMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s : Fin (min (coupledLabel l m r) n+1)) :
    RealQuantumSpace (coupledLabel (coupledLabel l m r) n s) →ₗ[ℝ] RealQuantumTripleSpace l m n :=
  (TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m r) 1).comp
    (unitaryQuantumClebschMap q hq hq1 (coupledLabel l m r) n s)

def quantumRightTreeMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1)) :
    RealQuantumSpace (coupledLabel l (coupledLabel m n u) v) →ₗ[ℝ] RealQuantumTripleSpace l m n :=
  (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).symm.toLinearMap.comp
    ((TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u)).comp
      (unitaryQuantumClebschMap q hq hq1 l (coupledLabel m n u) v))

theorem quantumLeftTensor_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (p v : RealQuantumSpace (coupledLabel l m r) ⊗[ℝ] RealQuantumSpace n) :
    quantumTripleBilin q l m n
      (TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m r) 1 p)
      (TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m r) 1 v)=
      quantumTensorBilin q (coupledLabel l m r) n p v := by
  exact tensorWeightedBilin_map_isometry
    (V:=RealQuantumSpace (coupledLabel l m r)) (W:=RealQuantumSpace n)
    (V':=RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) (W':=RealQuantumSpace n)
    (standardWeightBasis (K:=ℝ) (coupledLabel l m r)) (standardWeightBasis (K:=ℝ) n)
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m))
    (standardWeightBasis (K:=ℝ) n)
    (fun i => quantumWeight q (coupledLabel l m r) i.val) (fun k => quantumWeight q n k.val)
    (fun ij => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val) (fun k => quantumWeight q n k.val)
    (unitaryQuantumClebschMap q hq hq1 l m r) 1
    (fun p v => by
      have h := unitaryQuantumClebschMap_isometry q hq hq1 l m r p v
      unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin quantumPair at h
      exact h) (fun _ _ => rfl) p v

theorem quantumRightTensor_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (p v : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace (coupledLabel m n u)) :
    quantumRightTripleBilin q l m n
      (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u) p)
      (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u) v)=
      quantumTensorBilin q l (coupledLabel m n u) p v := by
  exact tensorWeightedBilin_map_isometry
    (V:=RealQuantumSpace l) (W:=RealQuantumSpace (coupledLabel m n u))
    (V':=RealQuantumSpace l) (W':=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
    (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) (coupledLabel m n u))
    (standardWeightBasis (K:=ℝ) l)
    ((standardWeightBasis (K:=ℝ) m).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) n))
    (fun i => quantumWeight q l i.val) (fun k => quantumWeight q (coupledLabel m n u) k.val)
    (fun i => quantumWeight q l i.val) (fun jk => quantumWeight q m jk.1.val*quantumWeight q n jk.2.val)
    1 (unitaryQuantumClebschMap q hq hq1 m n u)
    (fun _ _ => rfl) (fun p v => by
      have h := unitaryQuantumClebschMap_isometry q hq hq1 m n u p v
      unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin quantumPair at h
      exact h) p v

theorem quantumLeftTreeMap_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s : Fin (min (coupledLabel l m r) n+1))
    (p v : RealQuantumSpace (coupledLabel (coupledLabel l m r) n s)) :
    quantumTripleBilin q l m n (quantumLeftTreeMap q hq hq1 l m n r s p)
      (quantumLeftTreeMap q hq hq1 l m n r s v)=quantumPair q (coupledLabel (coupledLabel l m r) n s) p v := by
  unfold quantumLeftTreeMap
  rw [LinearMap.comp_apply,LinearMap.comp_apply,quantumLeftTensor_isometry,
    unitaryQuantumClebschMap_isometry]

theorem quantumRightTreeMap_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1))
    (p w : RealQuantumSpace (coupledLabel l (coupledLabel m n u) v)) :
    quantumTripleBilin q l m n (quantumRightTreeMap q hq hq1 l m n u v p)
      (quantumRightTreeMap q hq hq1 l m n u v w)=quantumPair q (coupledLabel l (coupledLabel m n u) v) p w := by
  unfold quantumRightTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [quantumTriple_assoc_symm_isometry,quantumRightTensor_isometry,unitaryQuantumClebschMap_isometry]

def quantumLeftTreeHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s : Fin (min (coupledLabel l m r) n+1)) : RealQuantumTripleSpace l m n :=
  quantumLeftTreeMap q hq hq1 l m n r s (standardWeightBasis (coupledLabel (coupledLabel l m r) n s) 0)

def quantumRightTreeHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1)) : RealQuantumTripleSpace l m n :=
  quantumRightTreeMap q hq hq1 l m n u v (standardWeightBasis (coupledLabel l (coupledLabel m n u) v) 0)

theorem quantumLeftTreeHighest_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s : Fin (min (coupledLabel l m r) n+1)) :
    quantumTripleBilin q l m n (quantumLeftTreeHighest q hq hq1 l m n r s)
      (quantumLeftTreeHighest q hq hq1 l m n r s)=1 := by
  unfold quantumLeftTreeHighest
  rw [quantumLeftTreeMap_isometry,quantumPair_basis,if_pos rfl]
  exact quantumWeight_zero q hq _

theorem quantumRightTreeHighest_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1)) :
    quantumTripleBilin q l m n (quantumRightTreeHighest q hq hq1 l m n u v)
      (quantumRightTreeHighest q hq hq1 l m n u v)=1 := by
  unfold quantumRightTreeHighest
  rw [quantumRightTreeMap_isometry,quantumPair_basis,if_pos rfl]
  exact quantumWeight_zero q hq _

/-- Independently constructed recoupling overlap in the positive-leading-coefficient coupling gauge.
It is defined from actual Uq modules and isometric CG maps, never from a Racah sum. -/
def quantumRacahEntry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s : Fin (min (coupledLabel l m r) n+1))
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1)) : ℝ :=
  quantumTripleBilin q l m n (quantumLeftTreeHighest q hq hq1 l m n r s)
    (quantumRightTreeHighest q hq hq1 l m n u v)

end AMSPhysical

#print axioms AMSPhysical.quantumRacahEntry
#print axioms AMSPhysical.quantumLeftTreeHighest_unit

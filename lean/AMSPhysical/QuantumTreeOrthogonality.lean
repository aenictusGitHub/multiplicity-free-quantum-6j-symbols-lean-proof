import QuantumRecouplingConstruction
import QuantumClebschOrthogonality
import TensorWeightedOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem quantumLeftTensor_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r s : Fin (min l m+1)) (hrs : r≠s)
    (p : RealQuantumSpace (coupledLabel l m r) ⊗[ℝ] RealQuantumSpace n)
    (v : RealQuantumSpace (coupledLabel l m s) ⊗[ℝ] RealQuantumSpace n) :
    quantumTripleBilin q l m n
      (TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m r) 1 p)
      (TensorProduct.map (unitaryQuantumClebschMap q hq hq1 l m s) 1 v)=0 := by
  apply tensorWeightedBilin_map_zero
    (V:=RealQuantumSpace (coupledLabel l m r)) (W:=RealQuantumSpace n)
    (U:=RealQuantumSpace (coupledLabel l m s)) (X:=RealQuantumSpace n)
    (V':=RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m) (W':=RealQuantumSpace n)
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m))
    (standardWeightBasis (K:=ℝ) n)
    (fun ij : Fin (l+1) × Fin (m+1) => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val)
    (fun k => quantumWeight q n k.val)
    (unitaryQuantumClebschMap q hq hq1 l m r) (unitaryQuantumClebschMap q hq hq1 l m s) 1 1
  intro a b c d
  have he := unitaryQuantumClebschMap_orthogonal q hq hq1 l m r s hrs a b
  unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin at he
  exact mul_eq_zero.mpr (Or.inl he)

theorem quantumRightTensor_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u v : Fin (min m n+1)) (huv : u≠v)
    (p : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace (coupledLabel m n u))
    (w : RealQuantumSpace l ⊗[ℝ] RealQuantumSpace (coupledLabel m n v)) :
    quantumRightTripleBilin q l m n
      (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n u) p)
      (TensorProduct.map 1 (unitaryQuantumClebschMap q hq hq1 m n v) w)=0 := by
  apply tensorWeightedBilin_map_zero
    (V:=RealQuantumSpace l) (W:=RealQuantumSpace (coupledLabel m n u))
    (U:=RealQuantumSpace l) (X:=RealQuantumSpace (coupledLabel m n v))
    (V':=RealQuantumSpace l) (W':=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
    (standardWeightBasis (K:=ℝ) l)
    ((standardWeightBasis (K:=ℝ) m).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) n))
    (fun i => quantumWeight q l i.val)
    (fun jk : Fin (m+1) × Fin (n+1) => quantumWeight q m jk.1.val*quantumWeight q n jk.2.val)
    1 1 (unitaryQuantumClebschMap q hq hq1 m n u) (unitaryQuantumClebschMap q hq hq1 m n v)
  intro a b c d
  have he := unitaryQuantumClebschMap_orthogonal q hq hq1 m n u v huv c d
  unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin at he
  exact mul_eq_zero.mpr (Or.inr he)

theorem quantumLeftTreeMap_outer_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r r' : Fin (min l m+1)) (hrr : r≠r')
    (s : Fin (min (coupledLabel l m r) n+1)) (s' : Fin (min (coupledLabel l m r') n+1))
    (p : RealQuantumSpace (coupledLabel (coupledLabel l m r) n s))
    (v : RealQuantumSpace (coupledLabel (coupledLabel l m r') n s')) :
    quantumTripleBilin q l m n (quantumLeftTreeMap q hq hq1 l m n r s p)
      (quantumLeftTreeMap q hq hq1 l m n r' s' v)=0 :=
  quantumLeftTensor_orthogonal q hq hq1 l m n r r' hrr _ _

theorem quantumLeftTreeMap_inner_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (r : Fin (min l m+1)) (s s' : Fin (min (coupledLabel l m r) n+1)) (hss : s≠s')
    (p : RealQuantumSpace (coupledLabel (coupledLabel l m r) n s))
    (v : RealQuantumSpace (coupledLabel (coupledLabel l m r) n s')) :
    quantumTripleBilin q l m n (quantumLeftTreeMap q hq hq1 l m n r s p)
      (quantumLeftTreeMap q hq hq1 l m n r s' v)=0 := by
  unfold quantumLeftTreeMap
  simp only [LinearMap.comp_apply]
  rw [quantumLeftTensor_isometry]
  exact unitaryQuantumClebschMap_orthogonal q hq hq1 (coupledLabel l m r) n s s' hss p v

theorem quantumRightTreeMap_outer_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u u' : Fin (min m n+1)) (huu : u≠u')
    (v : Fin (min l (coupledLabel m n u)+1)) (v' : Fin (min l (coupledLabel m n u')+1))
    (p : RealQuantumSpace (coupledLabel l (coupledLabel m n u) v))
    (w : RealQuantumSpace (coupledLabel l (coupledLabel m n u') v')) :
    quantumTripleBilin q l m n (quantumRightTreeMap q hq hq1 l m n u v p)
      (quantumRightTreeMap q hq hq1 l m n u' v' w)=0 := by
  unfold quantumRightTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [quantumTriple_assoc_symm_isometry]
  exact quantumRightTensor_orthogonal q hq hq1 l m n u u' huu _ _

theorem quantumRightTreeMap_inner_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v v' : Fin (min l (coupledLabel m n u)+1)) (hvv : v≠v')
    (p : RealQuantumSpace (coupledLabel l (coupledLabel m n u) v))
    (w : RealQuantumSpace (coupledLabel l (coupledLabel m n u) v')) :
    quantumTripleBilin q l m n (quantumRightTreeMap q hq hq1 l m n u v p)
      (quantumRightTreeMap q hq hq1 l m n u v' w)=0 := by
  unfold quantumRightTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [quantumTriple_assoc_symm_isometry,quantumRightTensor_isometry]
  exact unitaryQuantumClebschMap_orthogonal q hq hq1 l (coupledLabel m n u) v v' hvv p w

end AMSPhysical

#print axioms AMSPhysical.quantumLeftTreeMap_inner_orthogonal
#print axioms AMSPhysical.quantumRightTreeMap_outer_orthogonal

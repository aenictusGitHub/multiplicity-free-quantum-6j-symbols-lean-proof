import StandardClebschAtLabel
import QuantumClebschOrthogonality
import BilinearMetricAdjoint
import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def standardClebschAdjoint (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L) :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ] finiteWeightSpace (K:=ℝ) L :=
  bilinearMetricAdjoint (quantumBilin q L) (quantumTensorBilin q l m) (quantumPair_definite q hq L)
    (standardClebschAtLabel q hq hq1 l m r L hL)

theorem standardClebschAdjoint_adjoint (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L)
    (v:finiteWeightSpace (K:=ℝ) L) (w:finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    quantumTensorBilin q l m (standardClebschAtLabel q hq hq1 l m r L hL v) w=
      quantumPair q L v (standardClebschAdjoint q hq hq1 l m r L hL w) :=
  bilinearMetricAdjoint_adjoint (quantumBilin q L) (quantumTensorBilin q l m)
    (quantumPair_definite q hq L) (quantumPair_symm q L)
    (fun u v=>finiteWeightedPair_symm _ _ u v) (standardClebschAtLabel q hq hq1 l m r L hL) v w

theorem standardClebschAdjoint_selected (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L) (v:finiteWeightSpace (K:=ℝ) L) :
    standardClebschAdjoint q hq hq1 l m r L hL (standardClebschAtLabel q hq hq1 l m r L hL v)=v :=
  bilinearMetricAdjoint_isometry_leftInverse _ _ (quantumPair_definite q hq L) (quantumPair_symm q L)
    (fun u v=>finiteWeightedPair_symm _ _ u v) _
    (standardClebschAtLabel_isometry q hq hq1 l m r L hL) v

theorem standardClebschAdjoint_other (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r s:Fin (min l m+1)) (hrs:r≠s) (L:ℕ) (hL:coupledLabel l m r=L)
    (v:finiteWeightSpace (K:=ℝ) (coupledLabel l m s)) :
    standardClebschAdjoint q hq hq1 l m r L hL (unitaryQuantumClebschMap q hq hq1 l m s v)=0 := by
  subst L
  apply quantumPair_definite q hq (coupledLabel l m r)
  rw [← standardClebschAdjoint_adjoint]
  exact unitaryQuantumClebschMap_orthogonal q hq hq1 l m r s hrs _ v

theorem standardClebschAdjoint_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L)
    (v:finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) (k:Fin (L+1)) :
    (standardWeightBasis (K:=ℝ) L).repr (standardClebschAdjoint q hq hq1 l m r L hL v) k=
      quantumTensorBilin q l m (standardClebschAtLabel q hq hq1 l m r L hL (standardWeightBasis L k)) v/
        quantumWeight q L k.val := by
  apply (eq_div_iff (ne_of_gt (quantumWeight_pos q hq L k.val))).mpr
  rw [standardClebschAdjoint_adjoint,quantumPair_symm]
  change _=finiteWeightedPair (fun i:Fin (L+1)=>quantumWeight q L i.val)
    (standardWeightBasis (K:=ℝ) L).equivFun.toLinearMap _ ((standardWeightBasis L) k)
  rw [finiteWeightedPair_basis_right]
  simp only [Module.Basis.equivFun_apply]
  ring

end AMSPhysical
#print axioms AMSPhysical.standardClebschAdjoint_coordinate

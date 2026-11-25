import QuantumHighestSpan
import QuantumFirstProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

variable {V W U : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

theorem representationCasimir_intertwines (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) : IsQuantumIntertwiner q ρ ρ (ρ (uqCasimir q)) := by
  intro x v
  have h := congrArg ρ (uqCasimir_central q hq x).eq
  simp only [map_mul] at h
  exact (DFunLike.congr_fun h v).symm

theorem tensor_map_right_scalar (T : W →ₗ[ℝ] U) (A : Module.End ℝ U) (a : ℝ)
    (h : ∀ w,A (T w)=a • T w) (p : V ⊗[ℝ] W) :
    TensorProduct.map (1 : Module.End ℝ V) A (TensorProduct.map 1 T p)=
      a • TensorProduct.map 1 T p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero,smul_zero]
  | tmul v w => simp only [TensorProduct.map_tmul,Module.End.one_apply,h,TensorProduct.tmul_smul]
  | add p v hp hv => simp only [map_add,hp,hv,smul_add]

def rightIntermediateCasimir (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    Module.End ℝ (RealQuantumTripleSpace l m n) :=
  (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).symm.toLinearMap.comp
    ((TensorProduct.map (1 : Module.End ℝ (RealQuantumSpace l))
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) m n (uqCasimir q))).comp
        (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).toLinearMap)

/-- The actual intermediate Casimir commutes with the total quantum action. -/
theorem rightIntermediateCasimir_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    IsQuantumIntertwiner (V:=RealQuantumTripleSpace l m n) (W:=RealQuantumTripleSpace l m n) q
      (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
      (finiteTripleRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m n)
      (rightIntermediateCasimir q hq hq1 l m n) := by
  let hd := qInteger_denominator_ne_zero q hq hq1
  let ρ := finiteTripleRepresentation q (ne_of_gt hq) hd l m n
  let σ := finiteRightTripleRepresentation q (ne_of_gt hq) hd l m n
  let A := TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)
  let C := TensorProduct.map (1 : Module.End ℝ (RealQuantumSpace l))
    (finiteTensorRepresentation q (ne_of_gt hq) hd m n (uqCasimir q))
  have ha := finiteTripleRepresentation_assoc q (ne_of_gt hq) hd l m n
  have hb := quantumIntertwiner_inverse
    (V:=RealQuantumTripleSpace l m n)
    (W:=RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)) q ρ σ A ha
  have hc : IsQuantumIntertwiner
      (V:=RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n))
      (W:=RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)) q σ σ C := by
    exact quantumIntertwiner_tensor
      (V:=RealQuantumSpace l) (W:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
      (V':=RealQuantumSpace l) (W':=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
      q (ne_of_gt hq) (finiteQuantumRepresentation q (ne_of_gt hq) hd l)
      (finiteTensorRepresentation q (ne_of_gt hq) hd m n)
      (finiteQuantumRepresentation q (ne_of_gt hq) hd l)
      (finiteTensorRepresentation q (ne_of_gt hq) hd m n) 1 _
      (fun _ _ => rfl) (representationCasimir_intertwines q (ne_of_gt hq) _)
  intro x v
  change ρ x (A.symm (C (A v)))=A.symm (C (A (ρ x v)))
  have hb' (w : RealQuantumSpace l ⊗[ℝ] (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)) :
      ρ x (A.symm w)=A.symm (σ x w) := hb x w
  have ha' : σ x (A v)=A (ρ x v) := ha x v
  rw [hb' _,hc x _,ha']

theorem firstTripleProjection_Casimir (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : RealQuantumTripleSpace l m n) :
    firstTripleProjection l m n (rightIntermediateCasimir q hq hq1 l m n p)=
      finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) m n (uqCasimir q)
        (firstTripleProjection l m n p) := by
  unfold firstTripleProjection rightIntermediateCasimir
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  exact tensorFirstProjection_map_right (V:=RealQuantumSpace l)
    (W:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n) (U:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n) _ _ _

theorem rightIntermediateCasimir_tree (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (u : Fin (min m n+1)) (v : Fin (min l (coupledLabel m n u)+1))
    (p : RealQuantumSpace (coupledLabel l (coupledLabel m n u) v)) :
    rightIntermediateCasimir q hq hq1 l m n (quantumRightTreeMap q hq hq1 l m n u v p)=
      quantumCasimirEigen q (coupledLabel m n u) • quantumRightTreeMap q hq hq1 l m n u v p := by
  unfold rightIntermediateCasimir quantumRightTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  rw [tensor_map_right_scalar (V:=RealQuantumSpace l) (W:=RealQuantumSpace (coupledLabel m n u))
    (U:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
    (unitaryQuantumClebschMap q hq hq1 m n u) _ (quantumCasimirEigen q (coupledLabel m n u))
    (quantumIntertwiner_Casimir (W:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n) q hq hq1
      (coupledLabel m n u) _ _ (unitaryQuantumClebschMap_intertwines q hq hq1 m n u)),map_smul]

/-- Self-adjointness uses the compact quantum metric, with its actual tensor associator. -/
theorem rightIntermediateCasimir_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ) :
    PairAdjoint (quantumTripleBilin q l m n) (rightIntermediateCasimir q hq hq1 l m n)
      (rightIntermediateCasimir q hq hq1 l m n) := by
  have ht := tensorWeightedBilin_adjoint_map
    (V:=RealQuantumSpace l) (W:=RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n)
    (standardWeightBasis (K:=ℝ) l) ((standardWeightBasis (K:=ℝ) m).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) n))
    (fun i => quantumWeight q l i.val)
    (fun jk : Fin (m+1) × Fin (n+1) => quantumWeight q m jk.1.val*quantumWeight q n jk.2.val)
    1 1 _ _ (PairAdjoint.id _)
    ((finiteQuantumTensor_compact q hq hq1 m n).casimir (ne_of_gt hq))
  intro p v
  let A := TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)
  let C := TensorProduct.map (1 : Module.End ℝ (RealQuantumSpace l))
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) m n (uqCasimir q))
  calc
    _=quantumRightTripleBilin q l m n (C (A p)) (A v) := by
      have he := quantumTriple_assoc_isometry q l m n (rightIntermediateCasimir q hq hq1 l m n p) v
      simpa only [rightIntermediateCasimir,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using he.symm
    _=quantumRightTripleBilin q l m n (A p) (C (A v)) := ht (A p) (A v)
    _=_ := by
      have he := quantumTriple_assoc_isometry q l m n p (rightIntermediateCasimir q hq hq1 l m n v)
      simpa only [rightIntermediateCasimir,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using he

end AMSPhysical

#print axioms AMSPhysical.rightIntermediateCasimir_intertwines
#print axioms AMSPhysical.rightIntermediateCasimir_adjoint
#print axioms AMSPhysical.rightIntermediateCasimir_tree

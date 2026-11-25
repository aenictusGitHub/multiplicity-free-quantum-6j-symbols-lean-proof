import FiniteWeightActions
import QuantumIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem quantumClebschMap_K_basis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r+1)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 2)
      (quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k))=
      q^((coupledLabel l m r:ℤ)-2*(k.val:ℤ)) •
        quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k) := by
  rw [quantumClebschMap_basis]
  have hK := finiteCoupledHighest_weight q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    l m r (channel_left_bound l m r) (channel_right_bound l m r)
  rw [← coupledLabel_cast l m r (channel_left_bound l m r) (channel_right_bound l m r)] at hK
  exact normalizedString_weight q (ne_of_gt hq)
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
    (coupledLabel l m r)
    (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r)) hK k.val

theorem quantumClebschMap_E_succ (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 0)
      (quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k.succ))=
      qInteger q (k.val+1:ℕ) •
        quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k.castSucc) := by
  rw [quantumClebschMap_basis,quantumClebschMap_basis]
  have hK := finiteCoupledHighest_weight q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    l m r (channel_left_bound l m r) (channel_right_bound l m r)
  rw [← coupledLabel_cast l m r (channel_left_bound l m r) (channel_right_bound l m r)] at hK
  have hE := finiteCoupledHighest_annihilated q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    l m r (channel_left_bound l m r) (channel_right_bound l m r)
    (fun j _ => ne_of_gt (qInteger_pos_real q hq hq1 (j+1:ℕ) (by omega)))
  exact normalizedString_E_succ q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
    (coupledLabel l m r)
    (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r))
    hE hK k.val k.isLt (fun j hj _ => ne_of_gt (qInteger_pos_real q hq hq1 j hj))

theorem quantumClebschMap_F_castSucc (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 1)
      (quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k.castSucc))=
      qInteger q ((coupledLabel l m r:ℤ)-(k.val:ℤ)) •
        quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k.succ) := by
  rw [quantumClebschMap_basis,quantumClebschMap_basis]
  exact normalizedString_F_succ q
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
    (coupledLabel l m r)
    (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r)) k.val k.isLt
    (fun j hj _ => ne_of_gt (qInteger_pos_real q hq hq1 j hj))

theorem quantumClebschMap_K (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 2)).comp
      (quantumClebschMap q hq hq1 l m r)=
      (quantumClebschMap q hq hq1 l m r).comp (finiteQuantumK q (coupledLabel l m r)) := by
  apply (standardWeightBasis (K:=ℝ) (coupledLabel l m r)).ext
  intro k
  simp only [LinearMap.comp_apply,standardWeightBasis_K,map_smul]
  exact quantumClebschMap_K_basis q hq hq1 l m r k

theorem quantumClebschMap_E (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 0)).comp
      (quantumClebschMap q hq hq1 l m r)=
      (quantumClebschMap q hq hq1 l m r).comp (finiteQuantumE q (coupledLabel l m r)) := by
  apply (standardWeightBasis (K:=ℝ) (coupledLabel l m r)).ext
  intro k
  simp only [LinearMap.comp_apply]
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [standardWeightBasis_E_zero,(quantumClebschMap q hq hq1 l m r).map_zero]
    exact quantumClebschMap_E_zero q hq hq1 l m r
  · rw [standardWeightBasis_E_succ,map_smul]
    exact quantumClebschMap_E_succ q hq hq1 l m r j

theorem quantumClebschMap_F (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 1)).comp
      (quantumClebschMap q hq hq1 l m r)=
      (quantumClebschMap q hq hq1 l m r).comp (finiteQuantumF q (coupledLabel l m r)) := by
  apply (standardWeightBasis (K:=ℝ) (coupledLabel l m r)).ext
  intro k
  simp only [LinearMap.comp_apply]
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [standardWeightBasis_F_last,(quantumClebschMap q hq hq1 l m r).map_zero]
    exact quantumClebschMap_F_top q hq hq1 l m r
  · rw [standardWeightBasis_F_castSucc,map_smul]
    exact quantumClebschMap_F_castSucc q hq hq1 l m r j

/-- The constructed injective Clebsch-Gordan map intertwines the entire independently
presented quantum algebra, not just its Casimir or weight operator. -/
theorem quantumClebschMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    IsQuantumIntertwiner (K:=ℝ) (V:=finiteWeightSpace (K:=ℝ) (coupledLabel l m r))
      (W:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (coupledLabel l m r))
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
      (quantumClebschMap q hq hq1 l m r) := by
  let A : UqSL2 q →ₐ[ℝ] Module.End ℝ (finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :=
    finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (coupledLabel l m r)
  let B : UqSL2 q →ₐ[ℝ] Module.End ℝ (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :=
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
  let T : finiteWeightSpace (K:=ℝ) (coupledLabel l m r) →ₗ[ℝ]
      finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m := quantumClebschMap q hq hq1 l m r
  have hA (i : Fin 4) : A (uqGenerator q i)=
      ![finiteQuantumE q (coupledLabel l m r),finiteQuantumF q (coupledLabel l m r),
        finiteQuantumK q (coupledLabel l m r),finiteQuantumKinv q (coupledLabel l m r)] i :=
    finiteQuantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (coupledLabel l m r) i
  have hK (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
      B (uqGenerator q 2) (T v)=T (A (uqGenerator q 2) v) := by
    rw [hA]
    exact DFunLike.congr_fun (quantumClebschMap_K q hq hq1 l m r) v
  refine quantumIntertwiner_of_generators (K:=ℝ)
    (V:=finiteWeightSpace (K:=ℝ) (coupledLabel l m r))
    (W:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) q A B T ?_
  intro i v
  fin_cases i
  · rw [hA]
    exact DFunLike.congr_fun (quantumClebschMap_E q hq hq1 l m r) v
  · rw [hA]
    exact DFunLike.congr_fun (quantumClebschMap_F q hq hq1 l m r) v
  · exact hK v
  · exact quantumKinv_intertwining (K:=ℝ)
      (V:=finiteWeightSpace (K:=ℝ) (coupledLabel l m r))
      (W:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) q A B T hK v

end AMSPhysical

#print axioms AMSPhysical.quantumClebschMap_intertwines

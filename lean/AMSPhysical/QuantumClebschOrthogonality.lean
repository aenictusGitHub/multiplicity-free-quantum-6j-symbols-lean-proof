import QuantumClebschIsometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem normalizedString_Casimir (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (L : ℕ) (v : V) (c : ℝ)
    (hv : ρ (uqCasimir q) v=c • v) (k : ℕ) :
    ρ (uqCasimir q) (normalizedString q ρ L v k)=c • normalizedString q ρ L v k := by
  unfold normalizedString
  rw [map_smul,representation_Casimir_Fpow q hq ρ c v hv k,smul_comm]

theorem quantumClebschMap_Casimir (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqCasimir q)
      (quantumClebschMap q hq hq1 l m r v)=
      quantumCasimirEigen q (coupledLabel l m r) • quantumClebschMap q hq hq1 l m r v := by
  let ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :=
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
  let T := quantumClebschMap q hq hq1 l m r
  have hC := finiteCoupledHighest_Casimir q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    l m r (channel_left_bound l m r) (channel_right_bound l m r)
    (fun j _ => ne_of_gt (qInteger_pos_real q hq hq1 (j+1:ℕ) (by omega)))
  rw [← coupledLabel_cast l m r (channel_left_bound l m r) (channel_right_bound l m r)] at hC
  have he : (ρ (uqCasimir q)).comp T=quantumCasimirEigen q (coupledLabel l m r) • T := by
    apply (standardWeightBasis (K:=ℝ) (coupledLabel l m r)).ext
    intro k
    change ρ (uqCasimir q) (T (standardWeightBasis (coupledLabel l m r) k))=
      quantumCasimirEigen q (coupledLabel l m r) • T (standardWeightBasis (coupledLabel l m r) k)
    dsimp only [T]
    rw [quantumClebschMap_basis]
    exact normalizedString_Casimir (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
      q (ne_of_gt hq) ρ (coupledLabel l m r) _ _ hC k.val
  exact DFunLike.congr_fun he v

theorem unitaryQuantumClebschMap_Casimir (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqCasimir q)
      (unitaryQuantumClebschMap q hq hq1 l m r v)=
      quantumCasimirEigen q (coupledLabel l m r) • unitaryQuantumClebschMap q hq hq1 l m r v := by
  change finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqCasimir q)
    ((Real.sqrt (quantumHighestNorm q l m r))⁻¹ • quantumClebschMap q hq hq1 l m r v)=
    quantumCasimirEigen q (coupledLabel l m r) •
      ((Real.sqrt (quantumHighestNorm q l m r))⁻¹ • quantumClebschMap q hq hq1 l m r v)
  rw [map_smul,quantumClebschMap_Casimir]
  exact smul_comm _ _ _

theorem channelCasimir_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) :
    Function.Injective (fun r : Fin (min l m+1) => quantumCasimirEigen q (coupledLabel l m r)) := by
  intro r s he
  have heq := quantumCasimirEigen_injective_real q hq hq1
    (show (coupledLabel l m r:ℤ)∈Set.Ici (0:ℤ) from Int.natCast_nonneg _)
    (show (coupledLabel l m s:ℤ)∈Set.Ici (0:ℤ) from Int.natCast_nonneg _) he
  rw [coupledLabel_cast l m r (channel_left_bound l m r) (channel_right_bound l m r),
    coupledLabel_cast l m s (channel_left_bound l m s) (channel_right_bound l m s)] at heq
  apply Fin.ext
  omega

theorem unitaryQuantumClebschMap_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r s : Fin (min l m+1)) (hrs : r≠s)
    (p : finiteWeightSpace (K:=ℝ) (coupledLabel l m r))
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m s)) :
    quantumTensorBilin q l m (unitaryQuantumClebschMap q hq hq1 l m r p)
      (unitaryQuantumClebschMap q hq hq1 l m s v)=0 := by
  exact pairAdjoint_eigen_orthogonal
    ((finiteQuantumTensor_compact q hq hq1 l m).casimir (ne_of_gt hq))
    _ _ _ _ (unitaryQuantumClebschMap_Casimir q hq hq1 l m r p)
    (unitaryQuantumClebschMap_Casimir q hq hq1 l m s v)
    (fun he => hrs (channelCasimir_injective q hq hq1 l m he))

end AMSPhysical

#print axioms AMSPhysical.unitaryQuantumClebschMap_orthogonal

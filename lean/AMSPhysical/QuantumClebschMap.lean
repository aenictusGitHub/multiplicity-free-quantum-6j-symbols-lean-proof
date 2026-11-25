import QuantumNormalizedStrings
import QuantumStringTruncation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

variable {K : Type*} [Field K]

def standardWeightVector (L : ℕ) (k : Fin (L+1)) : finiteWeightSpace (K:=K) L :=
  finiteWeightVector L (k.val:ℤ) (by have hk := k.isLt; constructor <;> omega)

theorem standardWeightVector_independent (L : ℕ) :
    LinearIndependent K (standardWeightVector (K:=K) L) := by
  apply LinearIndependent.of_comp (finiteWeightSpace (K:=K) L).subtype
  change LinearIndependent K (fun k : Fin (L+1) => Finsupp.single (k.val:ℤ) (1:K))
  apply (Finsupp.linearIndependent_single_one (ι:=ℤ) (R:=K)).comp
  intro i j he
  dsimp only at he
  apply Fin.ext
  exact_mod_cast he

def standardWeightBasis (L : ℕ) : Basis (Fin (L+1)) K (finiteWeightSpace (K:=K) L) :=
  basisOfLinearIndependentOfCardEqFinrank (K:=K) (V:=finiteWeightSpace (K:=K) L)
    (standardWeightVector_independent L) (by rw [Fintype.card_fin,finiteWeightSpace_finrank])

theorem standardWeightBasis_apply (L : ℕ) (k : Fin (L+1)) :
    standardWeightBasis (K:=K) L k=standardWeightVector L k := by simp [standardWeightBasis]

def quantumClebschMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : Fin (min l m+1)) :
    finiteWeightSpace (K:=ℝ) (coupledLabel l m r) →ₗ[ℝ]
      finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m :=
  (standardWeightBasis (coupledLabel l m r)).constr ℝ (fun k =>
    normalizedString q
      (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
      (coupledLabel l m r)
      (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r)) k)

theorem quantumClebschMap_basis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r+1)) :
    quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k)=
      normalizedString q
        (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
        (coupledLabel l m r)
        (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r)) k := by
  simp only [quantumClebschMap,Basis.constr_basis]

theorem quantumClebschMap_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m : ℕ) (r : Fin (min l m+1)) : Function.Injective (quantumClebschMap q hq hq1 l m r) := by
  classical
  have hraw : LinearIndependent ℝ (realCoupledVector q hq hq1 l m r) :=
    (realCoupledVector_independent q hq hq1 l m).comp
      (fun k => (⟨r,k⟩ : CoupledIndex l m)) (fun i j he => eq_of_heq (Sigma.mk.inj he).2)
  have hfall (k : Fin (coupledLabel l m r+1)) : qFalling q (coupledLabel l m r) k≠0 :=
    qFalling_ne_zero q (coupledLabel l m r) k (by have hk := k.isLt; omega)
      (fun j hj _ => ne_of_gt (qInteger_pos_real q hq hq1 j hj))
  have hnorm := hraw.units_smul (fun k => Units.mk0 (qFalling q (coupledLabel l m r) k)⁻¹
    (inv_ne_zero (hfall k)))
  refine LinearMap.injective_of_linearIndependent (R:=ℝ)
    (M:=finiteWeightSpace (K:=ℝ) (coupledLabel l m r))
    (N:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (f:=quantumClebschMap q hq hq1 l m r)
    (v:=standardWeightBasis (K:=ℝ) (coupledLabel l m r))
    (standardWeightBasis (K:=ℝ) (coupledLabel l m r)).span_eq ?_
  simpa only [Function.comp_def,quantumClebschMap_basis,normalizedString,realCoupledVector,
    coupledString,Pi.smul_apply',Units.smul_def,Units.val_mk0] using hnorm

theorem quantumClebschMap_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 0)
      (quantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) 0))=0 := by
  rw [quantumClebschMap_basis]
  simp only [Fin.val_zero]
  rw [normalizedString_zero]
  exact finiteCoupledHighest_annihilated q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    l m r (channel_left_bound l m r) (channel_right_bound l m r)
    (fun j _ => ne_of_gt (qInteger_pos_real q hq hq1 (j+1:ℕ) (by omega)))

theorem quantumClebschMap_F_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m (uqGenerator q 1)
      (quantumClebschMap q hq hq1 l m r
        (standardWeightBasis (coupledLabel l m r) (Fin.last (coupledLabel l m r))))=0 := by
  rw [quantumClebschMap_basis]
  simp only [Fin.val_last]
  apply normalizedString_F_top q
    (finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m)
    (coupledLabel l m r)
    (finiteCoupledHighest q l m r (channel_left_bound l m r) (channel_right_bound l m r))
  exact coupledString_truncates q hq hq1 l m r

end AMSPhysical

#print axioms AMSPhysical.quantumClebschMap_injective
#print axioms AMSPhysical.quantumClebschMap_F_top

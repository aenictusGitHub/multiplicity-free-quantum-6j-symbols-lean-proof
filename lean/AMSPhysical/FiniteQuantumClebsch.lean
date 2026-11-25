import QuantumClebschClosed
import QuantumTensorRepresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

def finiteTensorForget (l m : ℕ) :
    finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m →ₗ[K]
      WeightModule K ⊗[K] WeightModule K :=
  TensorProduct.map (finiteWeightSpace l).subtype (finiteWeightSpace m).subtype

theorem finiteTensorForget_injective (l m : ℕ) :
    Function.Injective (finiteTensorForget (K:=K) l m) :=
  TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective

def finiteCoupledHighest (q : K) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m :=
  ∑ k : Fin (r+1),couplingCoefficient q m r k •
    (finiteWeightVector l (k:ℤ) (by have hk := k.isLt; constructor <;> omega) ⊗ₜ[K]
      finiteWeightVector m ((r:ℤ)-k) (by have hk := k.isLt; constructor <;> omega))

theorem finiteCoupledHighest_forget (q : K) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    finiteTensorForget l m (finiteCoupledHighest q l m r hl hm)=coupledHighest q m r := by
  simp only [finiteCoupledHighest,map_sum,map_smul,finiteTensorForget,TensorProduct.map_tmul,
    finiteWeightVector,Submodule.subtype_apply]
  change (∑ k : Fin (r+1),couplingCoefficient q m r k • tensorWeightBasis (k:ℤ) ((r:ℤ)-k))=
    ∑ k∈Finset.range (r+1),couplingCoefficient q m r k • tensorWeightBasis (k:ℤ) ((r:ℤ)-k)
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => couplingCoefficient q m r k • tensorWeightBasis (K:=K) (k:ℤ) ((r:ℤ)-k)) (r+1)

theorem finiteTensor_E_forget (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l m : ℕ)
    (v : finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m) :
    finiteTensorForget l m (finiteTensorRepresentation q hq hden l m (uqGenerator q 0) v)=
      tensorQuantumE q m (finiteTensorForget l m v) := by
  have he : (finiteTensorForget (K:=K) l m).comp
      (finiteTensorRepresentation q hq hden l m (uqGenerator q 0))=
      (tensorQuantumE q m).comp (finiteTensorForget l m) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change finiteTensorForget l m
      (tensorRepresentation q hq (finiteQuantumRepresentation q hq hden l)
        (finiteQuantumRepresentation q hq hden m) (uqGenerator q 0) (x ⊗ₜ[K] y))=_
    rw [tensorRepresentation_E]
    simp [finiteTensorForget,uqGenerator,finiteQuantumRepresentation_generator,tensorQuantumE,
      finiteQuantumE,finiteQuantumK,restrictWeightEnd,TensorProduct.map_tmul]
  exact congrArg (fun f => f v) he

/-- Nonzero Clebsch-Gordan highest-weight vector in the actual finite tensor representation. -/
theorem finiteCoupledHighest_annihilated (q : K) (hq : q≠0) (hden : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m)
    (hqi : ∀ k∈Finset.range r,qInteger q (k+1:ℕ)≠0) :
    finiteTensorRepresentation q hq hden l m (uqGenerator q 0)
      (finiteCoupledHighest q l m r hl hm)=0 := by
  apply finiteTensorForget_injective l m
  rw [finiteTensor_E_forget,finiteCoupledHighest_forget,coupledHighest_annihilated q hq m r hqi,map_zero]

theorem finiteCoupledHighest_ne_zero (q : K) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    finiteCoupledHighest q l m r hl hm≠0 := by
  intro he
  have hh := finiteCoupledHighest_forget q l m r hl hm
  rw [he,map_zero] at hh
  exact coupledHighest_ne_zero q m r hh.symm

end AMSPhysical

#print axioms AMSPhysical.finiteCoupledHighest_annihilated
#print axioms AMSPhysical.finiteCoupledHighest_ne_zero

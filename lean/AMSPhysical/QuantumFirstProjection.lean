import QuantumHighestReconstruction
import QuantumClebschSingleSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {V W U : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

def tensorFirstProjection (φ : V →ₗ[ℝ] ℝ) : V ⊗[ℝ] W →ₗ[ℝ] W :=
  (TensorProduct.lid ℝ W).toLinearMap.comp (TensorProduct.map φ 1)

theorem tensorFirstProjection_tmul (φ : V →ₗ[ℝ] ℝ) (v : V) (w : W) :
    tensorFirstProjection φ (v ⊗ₜ[ℝ] w)=φ v • w := by
  simp only [tensorFirstProjection,LinearMap.comp_apply,TensorProduct.map_tmul,
    Module.End.one_apply,LinearEquiv.coe_coe,TensorProduct.lid_tmul]

theorem tensorFirstProjection_map_right (φ : V →ₗ[ℝ] ℝ) (T : W →ₗ[ℝ] U) (p : V ⊗[ℝ] W) :
    tensorFirstProjection φ (TensorProduct.map 1 T p)=T (tensorFirstProjection φ p) := by
  have he : (tensorFirstProjection (W:=U) φ).comp (TensorProduct.map 1 T)=
      T.comp (tensorFirstProjection (W:=W) φ) := by
    apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul,Module.End.one_apply,
      tensorFirstProjection_tmul,map_smul]
  exact DFunLike.congr_fun he p

def firstWeightFunctional (L : ℕ) : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (0:ℤ)).comp (finiteWeightSpace (K:=ℝ) L).subtype

def finiteFirstProjection (l m : ℕ) :
    RealQuantumSpace l ⊗[ℝ] RealQuantumSpace m →ₗ[ℝ] RealQuantumSpace m :=
  tensorFirstProjection (firstWeightFunctional l)

def firstTripleProjection (l m n : ℕ) : RealQuantumTripleSpace l m n →ₗ[ℝ]
    (RealQuantumSpace m ⊗[ℝ] RealQuantumSpace n) :=
  (tensorFirstProjection (firstWeightFunctional l)).comp
    (TensorProduct.assoc ℝ (RealQuantumSpace l) (RealQuantumSpace m) (RealQuantumSpace n)).toLinearMap

theorem firstWeightFunctional_basis (L : ℕ) (k : Fin (L+1)) :
    firstWeightFunctional L (standardWeightBasis L k)=if k.val=0 then 1 else 0 := by
  rw [standardWeightBasis_apply]
  change Finsupp.single (k.val:ℤ) (1:ℝ) 0=_
  simp only [Finsupp.single_apply]
  congr 1
  exact propext ⟨fun h => by exact_mod_cast h,fun h => by exact_mod_cast h⟩

theorem finiteFirstProjection_highest (q : ℝ) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    finiteFirstProjection l m (finiteCoupledHighest q l m r hl hm)=
      standardWeightBasis m (⟨r,by omega⟩ : Fin (m+1)) := by
  rw [finiteCoupledHighest_basis,map_sum]
  rw [Finset.sum_eq_single (0 : Fin (r+1))]
  · rw [map_smul,Basis.tensorProduct_apply']
    change couplingCoefficient q m r 0 •
      tensorFirstProjection (firstWeightFunctional l)
        (standardWeightBasis l (couplingBasisIndex l m r hl hm 0).1 ⊗ₜ[ℝ]
          standardWeightBasis m (couplingBasisIndex l m r hl hm 0).2)=_
    rw [tensorFirstProjection_tmul,firstWeightFunctional_basis]
    simp only [couplingCoefficient,couplingBasisIndex,Fin.val_zero,ite_true,one_smul,Nat.sub_zero]
  · intro k hk hk0
    rw [map_smul,Basis.tensorProduct_apply']
    change couplingCoefficient q m r k.val •
      tensorFirstProjection (firstWeightFunctional l)
        (standardWeightBasis l (couplingBasisIndex l m r hl hm k).1 ⊗ₜ[ℝ]
          standardWeightBasis m (couplingBasisIndex l m r hl hm k).2)=0
    rw [tensorFirstProjection_tmul,firstWeightFunctional_basis]
    have hkn : k.val≠0 := fun h => hk0 (Fin.ext h)
    simp only [couplingBasisIndex,if_neg hkn,zero_smul,smul_zero]
  · intro h
    exact (h (Finset.mem_univ 0)).elim

theorem unitaryClebsch_highest_firstProjection (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    finiteFirstProjection l m
      (unitaryQuantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) 0))=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹ •
        standardWeightBasis m (⟨r.val,by have hh := channel_right_bound l m r;omega⟩ : Fin (m+1)) := by
  unfold unitaryQuantumClebschMap
  rw [LinearMap.smul_apply,map_smul,quantumClebschMap_highest,finiteFirstProjection_highest]

end AMSPhysical

#print axioms AMSPhysical.unitaryClebsch_highest_firstProjection

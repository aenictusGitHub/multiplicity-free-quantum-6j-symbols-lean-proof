import TwoVertexTensorEmbedding
import OccupationTensorCoefficients
import TensorBasisSlices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoRowFirstOccupation (n : ℕ) (hn : 0<n) (l r : ℕ) (hl : r≤l) (k : Fin (r+1)) :
    occupationWeights (Fin (n+1)) l :=
  twoVertexOccupation n hn l ⟨k.val,by have hk:=k.isLt;omega⟩

def twoRowSecondOccupation (n : ℕ) (hn : 0<n) (m r : ℕ) (hm : r≤m) (k : Fin (r+1)) :
    occupationWeights (Fin (n+1)) m :=
  twoVertexOccupation n hn m ⟨r-k.val,by have hk:=k.isLt;omega⟩

theorem twoRowFirstOccupation_injective (n : ℕ) (hn : 0<n) (l r : ℕ) (hl : r≤l) :
    Function.Injective (twoRowFirstOccupation n hn l r hl) := by
  intro i j h
  have he := twoVertexOccupation_injective n hn l h
  apply Fin.ext
  exact congrArg (fun z : Fin (l+1) => z.val) he

theorem twoRowFirstOccupation_zero (n : ℕ) (hn : 0<n) (l r : ℕ) (hl : r≤l) :
    twoRowFirstOccupation n hn l r hl 0=highestOccupation n l := twoVertexOccupation_zero n hn l

theorem twoRowSecondOccupation_zero (n : ℕ) (hn : 0<n) (m r : ℕ) (hm : r≤m) :
    twoRowSecondOccupation n hn m r hm 0=twoVertexOccupation n hn m ⟨r,by omega⟩ := rfl

theorem twoRowHighest_sum (q : ℝ) (n : ℕ) (hn : 0<n) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    twoRowHighest q n hn l m r hl hm=
      ∑ k : Fin (r+1),couplingCoefficient q (m:ℤ) r k.val •
        (quantumOccupationBasis (K:=ℝ) l (twoRowFirstOccupation n hn l r hl k) ⊗ₜ[ℝ]
          quantumOccupationBasis (K:=ℝ) m (twoRowSecondOccupation n hn m r hm k)) := by
  unfold twoRowHighest
  rw [finiteCoupledHighest_basis]
  simp only [map_sum,map_smul,twoVertexTensorEmbedding,Module.Basis.tensorProduct_apply',
    TensorProduct.map_tmul,twoVertexEmbedding_basis]
  rfl

theorem twoRowHighest_boundary_coefficient (q : ℝ) (n : ℕ) (hn : 0<n) (l m r : ℕ)
    (hl : r≤l) (hm : r≤m) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (twoRowHighest q n hn l m r hl hm)
      ((highestOccupation n l).val,y.val)=(if twoVertexOccupation n hn m ⟨r,by omega⟩=y then 1 else 0) := by
  classical
  rw [occupationTensorCoefficients_repr,twoRowHighest_sum]
  have h := tensor_sum_left_coefficient
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (twoRowFirstOccupation n hn l r hl) (twoRowFirstOccupation_injective n hn l r hl)
    (fun k : Fin (r+1) => couplingCoefficient q (m:ℤ) r k.val)
    (fun k => quantumOccupationBasis (K:=ℝ) m (twoRowSecondOccupation n hn m r hm k))
    (0 : Fin (r+1)) y
  rw [twoRowFirstOccupation_zero,twoRowSecondOccupation_zero,Module.Basis.repr_self] at h
  simp only [Fin.val_zero,couplingCoefficient,one_mul,Finsupp.single_apply,← TensorProduct.smul_tmul'] at h
  exact h

end AMSPhysical

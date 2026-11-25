import TwoVertexCreationCompression
import QuantumCreationBoundary
import QuantumCreationGeneralShift

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexOccupation_shift_zero (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    shiftedOccupation n L 1 0 (twoVertexOccupation n hn L k)=
      twoVertexOccupation n hn (L+1) k.castSucc := by
  apply Subtype.ext
  funext j
  by_cases hj0:j=0
  · subst j
    change (twoVertexOccupation n hn L k).val 0+1=_
    rw [twoVertexOccupation_first,twoVertexOccupation_first]
    have hk:=k.isLt
    simp only [Fin.coe_castSucc]
    omega
  · by_cases hj1:j=secondVertex n hn
    · subst j
      simp only [shiftedOccupation,Pi.add_apply,Pi.single_apply,Ne.symm (secondVertex_ne_zero n hn),if_false,add_zero]
      rw [twoVertexOccupation_second,twoVertexOccupation_second]
      rfl
    · change (twoVertexOccupation n hn L k).val j+(Pi.single (0:Fin (n+1)) (1:ℤ):Fin (n+1) → ℤ) j=_
      rw [twoVertexOccupation_other n hn L k j hj0 hj1,twoVertexOccupation_other n hn (L+1) k.castSucc j hj0 hj1]
      simp [Pi.single_apply,hj0,Ne.symm hj0]

theorem twoVertexOccupation_shift_second (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    shiftedOccupation n L 1 (secondVertex n hn) (twoVertexOccupation n hn L k)=
      twoVertexOccupation n hn (L+1) k.succ := by
  apply Subtype.ext
  funext j
  by_cases hj0:j=0
  · subst j
    change (twoVertexOccupation n hn L k).val 0+(Pi.single (secondVertex n hn) (1:ℤ):Fin (n+1) → ℤ) 0=_
    simp only [Pi.single_apply,secondVertex_ne_zero n hn,Ne.symm (secondVertex_ne_zero n hn),if_false,add_zero]
    rw [twoVertexOccupation_first,twoVertexOccupation_first]
    have hk:=k.isLt
    simp only [Fin.val_succ]
    omega
  · by_cases hj1:j=secondVertex n hn
    · subst j
      change (twoVertexOccupation n hn L k).val (secondVertex n hn)+1=_
      rw [twoVertexOccupation_second,twoVertexOccupation_second]
      simp
    · change (twoVertexOccupation n hn L k).val j+(Pi.single (secondVertex n hn) (1:ℤ):Fin (n+1) → ℤ) j=_
      rw [twoVertexOccupation_other n hn L k j hj0 hj1,twoVertexOccupation_other n hn (L+1) k.succ j hj0 hj1]
      simp [Pi.single_apply,hj1,Ne.symm hj1]

theorem twoVertexOccupation_shift_other (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1))
    (j : Fin (n+1)) (hj0:j≠0) (hj1:j≠secondVertex n hn) :
    ¬∃ u : Fin (L+2),shiftedOccupation n L 1 j (twoVertexOccupation n hn L k)=
      twoVertexOccupation n hn (L+1) u := by
  rintro ⟨u,hu⟩
  have he:=congrArg (fun x : occupationWeights (Fin (n+1)) (L+1) =>x.val j) hu
  dsimp only at he
  change (twoVertexOccupation n hn L k).val j+(Pi.single j (1:ℤ):Fin (n+1) → ℤ) j=(twoVertexOccupation n hn (L+1) u).val j at he
  simp only [Pi.single_eq_same] at he
  rw [twoVertexOccupation_other n hn L k j hj0 hj1,twoVertexOccupation_other n hn (L+1) u j hj0 hj1] at he
  norm_num at he

theorem twoVertexOccupation_prefix_second (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    occupationPrefix n (secondVertex n hn) (twoVertexOccupation n hn L k).val=(L:ℤ) := by
  change occupationPrefix n (secondVertex n hn)
    (Pi.single 0 ((L-k.val:ℕ):ℤ)+Pi.single (secondVertex n hn) (k.val:ℤ))=_
  rw [occupationPrefix_add,occupationPrefix_single_scalar,occupationPrefix_single_scalar]
  simp only [Fin.val_zero,Nat.zero_le,if_true,le_refl]
  have hk:=k.isLt
  omega

theorem mixedCreationCoefficient_twoVertex_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (i : Fin (l+1)) (j : Fin (m+1)) :
    mixedCreationCoefficient q n 0 ((twoVertexOccupation n hn l i).val,(twoVertexOccupation n hn m j).val)=
      q^(-((l-i.val:ℕ):ℤ)-((m-j.val:ℕ):ℤ)) := by
  simp only [mixedCreationCoefficient,Fin.val_zero,Nat.cast_zero,neg_zero,pow_zero,one_mul,
    occupationPrefix_zero,twoVertexOccupation_first,zero_sub]

theorem mixedCreationCoefficient_twoVertex_second (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (i : Fin (l+1)) (j : Fin (m+1)) :
    mixedCreationCoefficient q n (secondVertex n hn) ((twoVertexOccupation n hn l i).val,(twoVertexOccupation n hn m j).val)=
      -(q^(-1-(l:ℤ)-(m:ℤ))) := by
  unfold mixedCreationCoefficient
  rw [twoVertexOccupation_prefix_second,twoVertexOccupation_prefix_second]
  change (-1:ℝ)^1*q^(-1-(l:ℤ)-(m:ℤ))=_
  rw [pow_one,neg_one_mul]

/-- The ACTUAL compressed physical creation map has only two terms, with
coefficients independent of rank. -/
theorem mixedTwoVertexCompressedCreation_basis (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (i : Fin (l+1)) (j : Fin (m+1)) :
    mixedTwoVertexCompressedCreation q n hn l m
      (standardWeightBasis (K:=ℝ) l i ⊗ₜ[ℝ] standardWeightBasis (K:=ℝ) m j)=
      q^(-((l-i.val:ℕ):ℤ)-((m-j.val:ℕ):ℤ)) •
        (standardWeightBasis (K:=ℝ) (l+1) i.castSucc ⊗ₜ[ℝ] standardWeightBasis (K:=ℝ) (m+1) j.castSucc)+
      (-(q^(-1-(l:ℤ)-(m:ℤ)))) •
        (standardWeightBasis (K:=ℝ) (l+1) i.succ ⊗ₜ[ℝ] standardWeightBasis (K:=ℝ) (m+1) j.succ) := by
  classical
  simp only [mixedTwoVertexCompressedCreation,LinearMap.comp_apply,twoVertexTensorEmbedding,
    TensorProduct.map_tmul,twoVertexEmbedding_basis,mixedFiniteCreation_basis,map_sum,map_smul]
  have he : (∑ k : Fin (n+1),mixedCreationCoefficient q n k
      ((twoVertexOccupation n hn l i).val,(twoVertexOccupation n hn m j).val) •
      twoVertexTensorProjection n hn (l+1) (m+1)
        (quantumOccupationBasis (K:=ℝ) (l+1) (shiftedOccupation n l 1 k (twoVertexOccupation n hn l i)) ⊗ₜ[ℝ]
          quantumOccupationBasis (K:=ℝ) (m+1) (shiftedOccupation n m 1 k (twoVertexOccupation n hn m j))))=
      ∑ k∈({0,secondVertex n hn}:Finset (Fin (n+1))),mixedCreationCoefficient q n k
      ((twoVertexOccupation n hn l i).val,(twoVertexOccupation n hn m j).val) •
      twoVertexTensorProjection n hn (l+1) (m+1)
        (quantumOccupationBasis (K:=ℝ) (l+1) (shiftedOccupation n l 1 k (twoVertexOccupation n hn l i)) ⊗ₜ[ℝ]
          quantumOccupationBasis (K:=ℝ) (m+1) (shiftedOccupation n m 1 k (twoVertexOccupation n hn m j))) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k hk hknot
    have hk0:k≠0:=by intro he; exact hknot (by simp [he])
    have hk1:k≠secondVertex n hn:=by intro he; exact hknot (by simp [he])
    simp only [twoVertexTensorProjection,TensorProduct.map_tmul]
    rw [twoVertexProjection_basis_outside n hn (l+1) _ (twoVertexOccupation_shift_other n hn l i k hk0 hk1),
      TensorProduct.zero_tmul,smul_zero]
  rw [he]
  simp only [Finset.sum_pair (Ne.symm (secondVertex_ne_zero n hn)),
    twoVertexOccupation_shift_zero,twoVertexOccupation_shift_second,
    twoVertexTensorProjection,TensorProduct.map_tmul,twoVertexProjection_basis_boundary,
    mixedCreationCoefficient_twoVertex_zero,mixedCreationCoefficient_twoVertex_second]

/-- Exact rank independence, proved from the actual physical creation map. -/
theorem mixedTwoVertexCompressedCreation_rank_independent (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    mixedTwoVertexCompressedCreation q n hn l m=mixedTwoVertexCompressedCreation q 1 (by omega) l m := by
  apply ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).ext
  rintro ⟨i,j⟩
  simp only [Module.Basis.tensorProduct_apply',mixedTwoVertexCompressedCreation_basis]

end AMSPhysical
#print axioms AMSPhysical.mixedTwoVertexCompressedCreation_rank_independent

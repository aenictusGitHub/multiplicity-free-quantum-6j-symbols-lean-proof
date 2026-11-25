import TwoRowFusionIndex

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoRowOccupationWeight (n : ℕ) (hn : 0<n) (l m r : ℕ) : Fin (n+1) → ℤ :=
  Pi.single 0 ((l+m-r:ℕ):ℤ)+Pi.single (secondVertex n hn) (r:ℤ)

def twoRowHighestWeight (n : ℕ) (hn : 0<n) (l m r : ℕ) : Fin n → ℤ :=
  simpleOccupationWeight n (twoRowOccupationWeight n hn l m r)

theorem twoRowOccupation_sum (n : ℕ) (hn : 0<n) (l m r : ℕ) (hl : r≤l) (hm : r≤m)
    (k : Fin (r+1)) :
    (twoRowFirstOccupation n hn l r hl k).val+(twoRowSecondOccupation n hn m r hm k).val=
      twoRowOccupationWeight n hn l m r := by
  funext j
  have hk:=k.isLt
  change (twoVertexOccupation n hn l ⟨k.val,by omega⟩).val j+
    (twoVertexOccupation n hn m ⟨r-k.val,by omega⟩).val j=_
  by_cases hj0 : j=0
  · subst j
    rw [twoVertexOccupation_first,twoVertexOccupation_first]
    simp only [twoRowOccupationWeight,Pi.add_apply,Pi.single_apply,ite_true,
      if_neg (secondVertex_ne_zero n hn),if_neg (Ne.symm (secondVertex_ne_zero n hn)),add_zero]
    omega
  · by_cases hj1 : j=secondVertex n hn
    · subst j
      rw [twoVertexOccupation_second,twoVertexOccupation_second]
      simp only [twoRowOccupationWeight,Pi.add_apply,Pi.single_apply,
        if_neg (Ne.symm (secondVertex_ne_zero n hn)),if_neg (secondVertex_ne_zero n hn),ite_true,zero_add]
      omega
    · rw [twoVertexOccupation_other n hn l _ j hj0 hj1,twoVertexOccupation_other n hn m _ j hj0 hj1]
      simp [twoRowOccupationWeight,Pi.single_apply,hj0,Ne.symm hj0,hj1,Ne.symm hj1]

theorem typeASymmetricTensor_K_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      q^(simpleOccupationWeight n x.val i+simpleOccupationWeight n y.val i) •
        (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y) := by
  have h : typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      typeAFiniteGenerator q hq hD n l i 2 (quantumOccupationBasis (K:=ℝ) l x) ⊗ₜ[ℝ]
        typeAFiniteGenerator q hq hD n m i 2 (quantumOccupationBasis (K:=ℝ) m y) := by
    simp [typeASymmetricTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductK,
      Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]
  rw [h,typeAFiniteGenerator_K_basis,typeAFiniteGenerator_K_basis]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [← zpow_add₀ hq]
  congr 1
  ring

theorem twoRowHighest_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (i : Fin n) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) (twoRowHighest q n hn l m r hl hm)=
      q^(twoRowHighestWeight n hn l m r i) • twoRowHighest q n hn l m r hl hm := by
  rw [twoRowHighest_sum,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul,typeASymmetricTensor_K_basis]
  have hWeight : simpleOccupationWeight n (twoRowFirstOccupation n hn l r hl k).val i+
      simpleOccupationWeight n (twoRowSecondOccupation n hn m r hm k).val i=twoRowHighestWeight n hn l m r i := by
    have he := congrArg (fun z => simpleOccupationWeight n z i) (twoRowOccupation_sum n hn l m r hl hm k)
    change simpleOccupationWeight n _ i=twoRowHighestWeight n hn l m r i at he
    rw [← he]
    simp only [simpleOccupationWeight,Pi.add_apply]
    ring
  rw [hWeight,smul_smul,smul_smul,mul_comm]

theorem twoRowHighestAt_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) (i : Fin n) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) (twoRowHighestAt q n hn l m r)=
      q^(twoRowHighestWeight n hn l m r.val i) • twoRowHighestAt q n hn l m r :=
  twoRowHighest_K q hq hD n hn l m r.val _ _ i

theorem twoRowHighestWeight_first (n : ℕ) (hn : 0<n) (l m r : ℕ) (hr : r≤l+m) :
    twoRowHighestWeight n hn l m r (⟨0,hn⟩ : Fin n)=(l:ℤ)+m-2*r := by
  change twoRowOccupationWeight n hn l m r 0-twoRowOccupationWeight n hn l m r (secondVertex n hn)=_
  simp only [twoRowOccupationWeight,Pi.add_apply,Pi.single_apply,ite_true,
    if_neg (secondVertex_ne_zero n hn),if_neg (Ne.symm (secondVertex_ne_zero n hn)),add_zero,zero_add]
  omega

theorem twoRowHighest_first_weight_injective (n : ℕ) (hn : 0<n) (l m : ℕ) :
    Function.Injective (fun r : TwoRowFusionIndex l m =>twoRowHighestWeight n hn l m r.val (⟨0,hn⟩ : Fin n)) := by
  intro r s he
  have hr:=r.isLt
  have hs:=s.isLt
  dsimp only at he
  rw [twoRowHighestWeight_first n hn l m r.val (by omega),twoRowHighestWeight_first n hn l m s.val (by omega)] at he
  apply Fin.ext
  omega

end AMSPhysical

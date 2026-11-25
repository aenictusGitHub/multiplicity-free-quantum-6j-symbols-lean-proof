import TwoVertexEmbedding
import QuantumOccupationLoweredAction
import QuantumTypeAPivotalWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem twoVertexOccupation_lowered_castSucc (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin L)
    (hi : 0<(twoVertexOccupation n hn L k.castSucc).val 0) :
    loweredOccupation n L (twoVertexOccupation n hn L k.castSucc) (⟨0,hn⟩ : Fin n) hi=
      twoVertexOccupation n hn L k.succ := by
  apply Subtype.ext
  funext j
  by_cases hj0 : j=0
  · subst j
    change (twoVertexOccupation n hn L k.castSucc).val 0-1=(twoVertexOccupation n hn L k.succ).val 0
    rw [twoVertexOccupation_first,twoVertexOccupation_first]
    have hk:=k.isLt
    simp only [Fin.val_succ,Fin.coe_castSucc]
    omega
  · by_cases hj1 : j=secondVertex n hn
    · subst j
      change (twoVertexOccupation n hn L k.castSucc).val (secondVertex n hn)+1=
        (twoVertexOccupation n hn L k.succ).val (secondVertex n hn)
      rw [twoVertexOccupation_second,twoVertexOccupation_second]
      simp only [Fin.val_succ,Fin.coe_castSucc,Nat.cast_add,Nat.cast_one]
    · change (twoVertexOccupation n hn L k.castSucc).val j+latticeRoot (secondVertex n hn) (0:Fin (n+1)) j=
        (twoVertexOccupation n hn L k.succ).val j
      rw [twoVertexOccupation_other n hn L k.castSucc j hj0 hj1,
        twoVertexOccupation_other n hn L k.succ j hj0 hj1,latticeRoot_other _ _ _ hj1 hj0]
      rfl

theorem twoVertexEmbedding_F (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : finiteWeightSpace (K:=ℝ) L) :
    twoVertexEmbedding n hn L (finiteQuantumF q L v)=
      typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 1 (twoVertexEmbedding n hn L v) := by
  have hMaps : (twoVertexEmbedding n hn L).comp (finiteQuantumF q L)=
      (typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 1).comp (twoVertexEmbedding n hn L) := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [LinearMap.comp_apply,standardWeightBasis_F_last,map_zero,twoVertexEmbedding_basis]
      rw [typeAFiniteGenerator_F_zero q hq hD n L _ (⟨0,hn⟩ : Fin n)
        (by change (twoVertexOccupation n hn L (Fin.last L)).val 0=0;rw [twoVertexOccupation_first];simp)]
    · simp only [LinearMap.comp_apply,standardWeightBasis_F_castSucc,map_smul,twoVertexEmbedding_basis]
      have hp : 0<(twoVertexOccupation n hn L j.castSucc).val 0 := by
        rw [twoVertexOccupation_first]
        have hj:=j.isLt
        simp only [Fin.coe_castSucc]
        omega
      rw [typeAFiniteGenerator_F_lowered q hq hD n L _ (⟨0,hn⟩ : Fin n) hp,
        twoVertexOccupation_lowered_castSucc]
      change qInteger q ((L:ℤ)-(j.val:ℤ)) • _=qInteger q ((twoVertexOccupation n hn L j.castSucc).val 0) • _
      rw [twoVertexOccupation_first]
      congr 2
      have hj:=j.isLt
      simp only [Fin.coe_castSucc]
      omega
  exact DFunLike.congr_fun hMaps v

theorem standardWeightBasis_Kinv (q : ℝ) (L : ℕ) (k : Fin (L+1)) :
    finiteQuantumKinv q L (standardWeightBasis L k)=
      q^(-((L:ℤ)-2*(k.val:ℤ))) • standardWeightBasis L k := by
  rw [standardWeightBasis_apply]
  apply Subtype.ext
  change quantumKinv q L (Finsupp.single (k.val:ℤ) 1)=
    q^(-((L:ℤ)-2*(k.val:ℤ))) • Finsupp.single (k.val:ℤ) 1
  simp only [quantumKinv,weightShift_single,add_zero,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one,Submodule.coe_smul]


theorem twoVertexEmbedding_Kinv (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : finiteWeightSpace (K:=ℝ) L) :
    twoVertexEmbedding n hn L (finiteQuantumKinv q L v)=
      typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 3 (twoVertexEmbedding n hn L v) := by
  have hMaps : (twoVertexEmbedding n hn L).comp (finiteQuantumKinv q L)=
      (typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 3).comp (twoVertexEmbedding n hn L) := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro k
    simp only [LinearMap.comp_apply,standardWeightBasis_Kinv,map_smul,twoVertexEmbedding_basis]
    rw [typeAFiniteGenerator_Ki_basis,twoVertexOccupation_simple]
  exact DFunLike.congr_fun hMaps v

end AMSPhysical
#print axioms AMSPhysical.twoVertexEmbedding_F
#print axioms AMSPhysical.twoVertexEmbedding_Kinv

import TwoVertexOccupation
import FiniteWeightActions
import QuantumOccupationLowering

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The literal first two-coordinate slice of the higher-rank symmetric
module, constructed from its actual occupation basis. -/
def twoVertexEmbedding (n : ℕ) (hn : 0<n) (L : ℕ) :
    finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L :=
  (standardWeightBasis (K:=ℝ) L).constr ℝ
    (fun k => quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L k))

@[simp] theorem twoVertexEmbedding_basis (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    twoVertexEmbedding n hn L (standardWeightBasis (K:=ℝ) L k)=
      quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L k) := by
  exact Module.Basis.constr_basis _ _ _ _

theorem twoVertexEmbedding_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : finiteWeightSpace (K:=ℝ) L) :
    twoVertexEmbedding n hn L (finiteQuantumE q L v)=
      typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 0 (twoVertexEmbedding n hn L v) := by
  have hMaps : (twoVertexEmbedding n hn L).comp (finiteQuantumE q L)=
      (typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 0).comp (twoVertexEmbedding n hn L) := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [LinearMap.comp_apply,standardWeightBasis_E_zero,map_zero,twoVertexEmbedding_basis]
      rw [twoVertexOccupation_zero,typeAFiniteGenerator_highest_E]
    · simp only [LinearMap.comp_apply,standardWeightBasis_E_succ,map_smul,twoVertexEmbedding_basis]
      have hp : 0<(twoVertexOccupation n hn L j.succ).val (secondVertex n hn) := by
        rw [twoVertexOccupation_second]
        simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
        omega
      rw [typeAFiniteGenerator_E_raised q hq hD n L _ (⟨0,hn⟩ : Fin n) hp,
        twoVertexOccupation_raised_succ]
      change qInteger q (j.val+1:ℕ) • quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L j.castSucc)=
        qInteger q ((twoVertexOccupation n hn L j.succ).val (secondVertex n hn)) •
          quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L j.castSucc)
      rw [twoVertexOccupation_second]
      rfl
  exact DFunLike.congr_fun hMaps v

theorem twoVertexEmbedding_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : finiteWeightSpace (K:=ℝ) L) :
    twoVertexEmbedding n hn L (finiteQuantumK q L v)=
      typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 2 (twoVertexEmbedding n hn L v) := by
  have hMaps : (twoVertexEmbedding n hn L).comp (finiteQuantumK q L)=
      (typeAFiniteGenerator q hq hD n L (⟨0,hn⟩ : Fin n) 2).comp (twoVertexEmbedding n hn L) := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro k
    simp only [LinearMap.comp_apply,standardWeightBasis_K,map_smul,twoVertexEmbedding_basis]
    rw [typeAFiniteGenerator_K_basis,twoVertexOccupation_simple]
  exact DFunLike.congr_fun hMaps v

theorem twoVertexEmbedding_E_other (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (L : ℕ)
    (i : Fin n) (hi : i≠(⟨0,hn⟩ : Fin n)) (v : finiteWeightSpace (K:=ℝ) L) :
    typeAFiniteGenerator q hq hD n L i 0 (twoVertexEmbedding n hn L v)=0 := by
  have hMaps : (typeAFiniteGenerator q hq hD n L i 0).comp (twoVertexEmbedding n hn L)=0 := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro k
    simp only [LinearMap.comp_apply,twoVertexEmbedding_basis,LinearMap.zero_apply]
    apply typeAFiniteGenerator_E_zero
    apply twoVertexOccupation_other
    · intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_succ,Fin.val_zero] at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      change i.val+1=1 at hv
      apply hi
      apply Fin.ext
      change i.val=0
      omega
  exact DFunLike.congr_fun hMaps v

end AMSPhysical

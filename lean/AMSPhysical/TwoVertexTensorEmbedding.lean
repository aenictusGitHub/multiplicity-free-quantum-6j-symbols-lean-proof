import TwoVertexIsometry
import QuantumSymmetricMetric
import QuantumHighestNorm
import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoVertexTensorEmbedding (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  TensorProduct.map (twoVertexEmbedding n hn l) (twoVertexEmbedding n hn m)

theorem twoVertexTensorEmbedding_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    twoVertexTensorEmbedding n hn l m (finiteTensorRepresentation q hq hD l m (uqGenerator q 0) v)=
      typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 0)
        (twoVertexTensorEmbedding n hn l m v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    have he : finiteTensorRepresentation q hq hD l m (uqGenerator q 0) (v ⊗ₜ[ℝ] w)=
        finiteQuantumE q l v ⊗ₜ[ℝ] finiteQuantumK q m w+v ⊗ₜ[ℝ] finiteQuantumE q m w := by
      simpa [finiteTensorRepresentation,uqGenerator,finiteQuantumRepresentation_generator] using
        tensorRepresentation_E q hq (finiteQuantumRepresentation q hq hD l)
          (finiteQuantumRepresentation q hq hD m) v w
    rw [he,map_add]
    simp only [twoVertexTensorEmbedding,TensorProduct.map_tmul]
    rw [typeASymmetricTensor_E_tmul,twoVertexEmbedding_E,twoVertexEmbedding_K,twoVertexEmbedding_E]
  | add v w hv hw => simp only [map_add,hv,hw]

theorem twoVertexTensorEmbedding_E_other (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (i : Fin n) (hi : i≠(⟨0,hn⟩ : Fin n))
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0)
      (twoVertexTensorEmbedding n hn l m v)=0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp only [twoVertexTensorEmbedding,TensorProduct.map_tmul]
    rw [typeASymmetricTensor_E_tmul,twoVertexEmbedding_E_other q hq hD n hn l i hi,
      twoVertexEmbedding_E_other q hq hD n hn m i hi,TensorProduct.zero_tmul,TensorProduct.tmul_zero,add_zero]
  | add v w hv hw => simp only [map_add,hv,hw,add_zero]

theorem twoVertexTensorEmbedding_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    symmetricTensorBilin q n l m (twoVertexTensorEmbedding n hn l m v) (twoVertexTensorEmbedding n hn l m w)=
      quantumTensorBilin q l m v w :=
  tensorWeightedBilin_map_isometry (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l) (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (fun k => quantumWeight q l k.val) (fun k => quantumWeight q m k.val)
    (occupationCompactWeight q n l) (occupationCompactWeight q n m)
    (twoVertexEmbedding n hn l) (twoVertexEmbedding n hn m)
    (twoVertexEmbedding_isometry q hq hq1 n hn l) (twoVertexEmbedding_isometry q hq hq1 n hn m) v w

/-- The physical two-row highest vector, obtained by applying an actual
isometric tensor embedding to the independently constructed rank-two CG vector. -/
def twoRowHighest (q : ℝ) (n : ℕ) (hn : 0<n) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  twoVertexTensorEmbedding n hn l m (finiteCoupledHighest q l m r hl hm)

theorem twoRowHighest_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (i : Fin n) :
    typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
      (typeAAlgebraGenerator q n i 0) (twoRowHighest q n hn l m r hl hm)=0 := by
  unfold twoRowHighest
  by_cases hi : i=(⟨0,hn⟩ : Fin n)
  · subst i
    rw [← twoVertexTensorEmbedding_E q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1),
      finiteCoupledHighest_annihilated q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m r hl hm,
      map_zero]
    intro k hk
    exact ne_of_gt (qInteger_pos_real q hq hq1 _ (by omega))
  · exact twoVertexTensorEmbedding_E_other q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m i hi _

theorem twoRowHighest_norm_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    symmetricTensorBilin q n l m (twoRowHighest q n hn l m r hl hm) (twoRowHighest q n hn l m r hl hm)=
      couplingNormClosed q (l-r) (m-r) r := by
  unfold twoRowHighest
  rw [twoVertexTensorEmbedding_isometry q hq hq1,finiteCoupledHighest_norm_closed_general q hq hq1]

end AMSPhysical

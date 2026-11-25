import InvariantQuantumForm
import CompactQuantumPair
import QuantumIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

def pullbackBilin (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] W) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := (B.comp T).compl₂ T

theorem quantumIntertwiner_pullback_EK (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (hρ : IsCompactQuantumPair (V:=W) q B ρ)
    (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (K:=ℝ) (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T) :
    PairAdjoint (pullbackBilin B T) (finiteQuantumE q L) (finiteQuantumK q L*finiteQuantumF q L) ∧
      PairAdjoint (pullbackBilin B T) (finiteQuantumK q L) (finiteQuantumK q L) := by
  have hg (i : Fin 4) : finiteQuantumRepresentation q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q i)=
      ![finiteQuantumE q L,finiteQuantumF q L,finiteQuantumK q L,finiteQuantumKinv q L] i :=
    finiteQuantumRepresentation_generator q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) L i
  have hgen (i : Fin 4) (v : finiteWeightSpace (K:=ℝ) L) := hT (uqGenerator q i) v
  simp only [hg] at hgen
  have hE (v : finiteWeightSpace (K:=ℝ) L) : ρ (uqGenerator q 0) (T v)=T (finiteQuantumE q L v) := by
    simpa only [Matrix.cons_val_zero] using hgen 0 v
  have hF (v : finiteWeightSpace (K:=ℝ) L) : ρ (uqGenerator q 1) (T v)=T (finiteQuantumF q L v) := by
    simpa only [Matrix.cons_val_one] using hgen 1 v
  have hK (v : finiteWeightSpace (K:=ℝ) L) : ρ (uqGenerator q 2) (T v)=T (finiteQuantumK q L v) := by
    simpa only [Matrix.cons_val_two] using hgen 2 v
  constructor
  · intro p v
    change B (T (finiteQuantumE q L p)) (T v)=B (T p) (T (finiteQuantumK q L (finiteQuantumF q L v)))
    rw [← hE p,hρ.adjE (T p) (T v)]
    change B (T p) (ρ (uqGenerator q 2) (ρ (uqGenerator q 1) (T v)))=_
    rw [hF v,hK (finiteQuantumF q L v)]
  · intro p v
    change B (T (finiteQuantumK q L p)) (T v)=B (T p) (T (finiteQuantumK q L v))
    rw [← hK p,hρ.adjK (T p) (T v),hK v]

/-- An actual algebra intertwiner scales the compact metric by exactly its highest-vector norm. -/
theorem quantumIntertwiner_metric (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (hρ : IsCompactQuantumPair (V:=W) q B ρ)
    (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (K:=ℝ) (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T)
    (p v : finiteWeightSpace (K:=ℝ) L) :
    B (T p) (T v)=B (T (standardWeightBasis L 0)) (T (standardWeightBasis L 0))*quantumPair q L p v := by
  obtain ⟨hE,hK⟩ := quantumIntertwiner_pullback_EK (W:=W) q hq hq1 L B ρ hρ T hT
  have he := quantumForm_unique q hq hq1 L (pullbackBilin B T) hE hK
  exact DFunLike.congr_fun (DFunLike.congr_fun he p) v

end AMSPhysical

#print axioms AMSPhysical.quantumIntertwiner_metric

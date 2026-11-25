import QuantumTensorPowers
import QuantumTensorIntertwiner
import QuantumCoupledStrings

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

theorem finiteQuantumForget_intertwines (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0) (L : ℕ) :
    IsQuantumIntertwiner (V:=finiteWeightSpace (K:=ℝ) L) (W:=WeightModule ℝ) q
      (finiteQuantumRepresentation q hq hd L) (quantumRepresentation q hq hd (L:ℤ))
      (finiteWeightSpace (K:=ℝ) L).subtype := by
  have hfin (i : Fin 4) : finiteQuantumRepresentation q hq hd L (uqGenerator q i)=
      ![finiteQuantumE q L,finiteQuantumF q L,finiteQuantumK q L,finiteQuantumKinv q L] i :=
    finiteQuantumRepresentation_generator q hq hd L i
  have hinf (i : Fin 4) : quantumRepresentation q hq hd (L:ℤ) (uqGenerator q i)=
      ![quantumE q,quantumF q L,quantumK q L,quantumKinv q L] i :=
    quantumRepresentation_generator q hq hd L i
  apply quantumIntertwiner_of_generators
  intro i v
  rw [hfin,hinf]
  fin_cases i <;> rfl

theorem finiteTensorForget_intertwines (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0) (l m : ℕ) :
    IsQuantumIntertwiner
      (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
      (W:=WeightModule ℝ ⊗[ℝ] WeightModule ℝ) q
      (finiteTensorRepresentation q hq hd l m)
      (tensorRepresentation q hq (quantumRepresentation q hq hd (l:ℤ)) (quantumRepresentation q hq hd (m:ℤ)))
      (finiteTensorForget (K:=ℝ) l m) :=
  quantumIntertwiner_tensor
    (V:=finiteWeightSpace (K:=ℝ) l) (W:=finiteWeightSpace (K:=ℝ) m)
    (V':=WeightModule ℝ) (W':=WeightModule ℝ) q hq
    (finiteQuantumRepresentation q hq hd l) (finiteQuantumRepresentation q hq hd m)
    (quantumRepresentation q hq hd l) (quantumRepresentation q hq hd m)
    (finiteWeightSpace l).subtype (finiteWeightSpace m).subtype
    (finiteQuantumForget_intertwines q hq hd l) (finiteQuantumForget_intertwines q hq hd m)

theorem infiniteTensor_F_end (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0) (l m : ℤ) :
    tensorRepresentation q hq (quantumRepresentation q hq hd l) (quantumRepresentation q hq hd m)
      (uqGenerator q 1)=tensorQuantumF q l m := by
  have hl (i : Fin 4) : quantumRepresentation q hq hd l (uqGenerator q i)=
      ![quantumE q,quantumF q l,quantumK q l,quantumKinv q l] i := quantumRepresentation_generator q hq hd l i
  have hm (i : Fin 4) : quantumRepresentation q hq hd m (uqGenerator q i)=
      ![quantumE q,quantumF q m,quantumK q m,quantumKinv q m] i := quantumRepresentation_generator q hq hd m i
  rw [tensorRepresentation_F_end (V:=WeightModule ℝ) (W:=WeightModule ℝ),hl 1,hl 3,hm 1]
  rfl

theorem coupledString_forget (q : ℝ) (hq : q≠0) (hd : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (a : ℕ) :
    finiteTensorForget l m (coupledString q hq hd l m r hl hm a)=
      ((tensorQuantumF q l m)^a) (coupledHighest q m r) := by
  have h := finiteTensorForget_intertwines q hq hd l m ((uqGenerator q 1)^a)
    (finiteCoupledHighest q l m r hl hm)
  simp only [map_pow] at h
  rw [infiniteTensor_F_end,finiteCoupledHighest_forget] at h
  exact h.symm

end AMSPhysical

#print axioms AMSPhysical.coupledString_forget

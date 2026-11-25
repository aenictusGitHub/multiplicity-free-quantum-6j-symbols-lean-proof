import QuantumCasimirBaseSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

theorem finiteTensor_K_forget (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l m : ℕ)
    (v : finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m) :
    finiteTensorForget l m (finiteTensorRepresentation q hq hden l m (uqGenerator q 2) v)=
      tensorQuantumK q l m (finiteTensorForget l m v) := by
  have he : (finiteTensorForget (K:=K) l m).comp
      (finiteTensorRepresentation q hq hden l m (uqGenerator q 2))=
      (tensorQuantumK q l m).comp (finiteTensorForget l m) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change finiteTensorForget l m
      (tensorRepresentation q hq (finiteQuantumRepresentation q hq hden l)
        (finiteQuantumRepresentation q hq hden m) (uqGenerator q 2) (x ⊗ₜ[K] y))=_
    rw [tensorRepresentation_K]
    simp [finiteTensorForget,uqGenerator,finiteQuantumRepresentation_generator,tensorQuantumK,
      finiteQuantumK,restrictWeightEnd,TensorProduct.map_tmul]
  exact congrArg (fun f => f v) he

theorem finiteCoupledHighest_weight (q : K) (hq : q≠0) (hden : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    finiteTensorRepresentation q hq hden l m (uqGenerator q 2) (finiteCoupledHighest q l m r hl hm)=
      q^((l:ℤ)+m-2*r) • finiteCoupledHighest q l m r hl hm := by
  apply finiteTensorForget_injective l m
  rw [finiteTensor_K_forget,finiteCoupledHighest_forget,map_smul,finiteCoupledHighest_forget,
    coupledHighest_weight q hq]

/-- Actual tensor-channel Casimir eigenvalue, derived from the constructed coupling vector. -/
theorem finiteCoupledHighest_Casimir (q : K) (hq : q≠0) (hden : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m)
    (hqi : ∀ k∈Finset.range r,qInteger q (k+1:ℕ)≠0) :
    finiteTensorRepresentation q hq hden l m (uqCasimir q) (finiteCoupledHighest q l m r hl hm)=
      quantumCasimirEigen q ((l:ℤ)+m-2*r) • finiteCoupledHighest q l m r hl hm := by
  let ρ : UqSL2 q →ₐ[K] Module.End K
      (finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m) :=
    finiteTensorRepresentation q hq hden l m
  let v := finiteCoupledHighest q l m r hl hm
  change ρ (uqCasimir q) v=quantumCasimirEigen q ((l:ℤ)+m-2*r) • v
  apply representation_Casimir_highest q hq ρ ((l:ℤ)+m-2*r) v
  · exact finiteCoupledHighest_annihilated q hq hden l m r hl hm hqi
  · exact finiteCoupledHighest_weight q hq hden l m r hl hm


end AMSPhysical

#print axioms AMSPhysical.finiteCoupledHighest_Casimir

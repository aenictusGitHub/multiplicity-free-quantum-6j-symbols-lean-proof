import QuantumStrings
import QuantumCasimirSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem representation_Casimir_Fpow (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (c : K) (v : V)
    (hv : ρ (uqCasimir q) v=c • v) (k : ℕ) :
    ρ (uqCasimir q) (((ρ (uqGenerator q 1))^k) v)=c • (((ρ (uqGenerator q 1))^k) v) := by
  have h := congrArg ρ ((uqCasimir_central q hq ((uqGenerator q 1)^k)).eq)
  simp only [map_mul,map_pow] at h
  have he := congrArg (fun T : Module.End K V => T v) h
  simpa only [Module.End.mul_apply,hv,map_smul] using he

def coupledLabel (l m r : ℕ) : ℕ := l+m-2*r

theorem coupledLabel_cast (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    (coupledLabel l m r:ℤ)=(l:ℤ)+m-2*r := by
  unfold coupledLabel
  omega

def coupledString (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (k : ℕ) :
    finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m :=
  ((finiteTensorRepresentation q hq hd l m (uqGenerator q 1))^k)
    (finiteCoupledHighest q l m r hl hm)

theorem coupledString_weight (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (k : ℕ) :
    finiteTensorRepresentation q hq hd l m (uqGenerator q 2) (coupledString q hq hd l m r hl hm k)=
      q^((l:ℤ)+m-2*r-2*k) • coupledString q hq hd l m r hl hm k := by
  exact representation_K_Fpow q hq (finiteTensorRepresentation q hq hd l m)
    ((l:ℤ)+m-2*r) (finiteCoupledHighest q l m r hl hm)
    (finiteCoupledHighest_weight q hq hd l m r hl hm) k

theorem coupledString_Casimir (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (k : ℕ)
    (hqi : ∀ j∈Finset.range r,qInteger q (j+1:ℕ)≠0) :
    finiteTensorRepresentation q hq hd l m (uqCasimir q) (coupledString q hq hd l m r hl hm k)=
      quantumCasimirEigen q ((l:ℤ)+m-2*r) • coupledString q hq hd l m r hl hm k := by
  exact representation_Casimir_Fpow q hq (finiteTensorRepresentation q hq hd l m)
    (quantumCasimirEigen q ((l:ℤ)+m-2*r)) (finiteCoupledHighest q l m r hl hm)
    (finiteCoupledHighest_Casimir q hq hd l m r hl hm hqi) k

theorem coupledString_ne_zero (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) (k : ℕ) (hk : k≤coupledLabel l m r)
    (hqi : ∀ j : ℤ,0<j → j≤((l+m:ℕ):ℤ) → qInteger q j≠0) :
    coupledString q hq hd l m r hl hm k≠0 := by
  let ρ : UqSL2 q →ₐ[K] Module.End K
      (finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m) :=
    finiteTensorRepresentation q hq hd l m
  let v := finiteCoupledHighest q l m r hl hm
  have hE := finiteCoupledHighest_annihilated q hq hd l m r hl hm (by
    intro j hj
    have hjr := Finset.mem_range.mp hj
    exact hqi (j+1:ℕ) (by omega) (by omega))
  have hK := finiteCoupledHighest_weight q hq hd l m r hl hm
  rw [← coupledLabel_cast l m r hl hm] at hK
  change ((ρ (uqGenerator q 1))^k) v≠0
  apply representation_Fpow_ne_zero q hq hd ρ (coupledLabel l m r) v
  · exact finiteCoupledHighest_ne_zero q l m r hl hm
  · exact hE
  · exact hK
  · intro j hj hjL
    exact hqi j hj (by unfold coupledLabel at hjL; omega)
  · exact hk

/-- Joint eigenvectors are independent when one operator separates channels and
the other separates weights within each channel. -/
theorem joint_eigenvectors_linearIndependent {ι : Type*} {κ : ι → Type*}
    (C H : Module.End K V) (c : ι → K) (hc : Function.Injective c)
    (w : ∀ i,κ i → K) (hw : ∀ i,Function.Injective (w i)) (v : ∀ i,κ i → V)
    (hv : ∀ i j,v i j≠0) (hC : ∀ i j,C (v i j)=c i • v i j)
    (hH : ∀ i j,H (v i j)=w i j • v i j) :
    LinearIndependent K (fun ij : Sigma κ => v ij.1 ij.2) := by
  have hi (i : ι) : LinearIndependent K (v i) :=
    H.eigenvectors_linearIndependent' (w i) (hw i) (v i)
      (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hH i j),hv i j⟩)
  have hs (i : ι) : Submodule.span K (Set.range (v i))≤C.eigenspace (c i) := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (hC i j)
  have hind : iSupIndep (fun i => Submodule.span K (Set.range (v i))) :=
    (C.eigenspaces_iSupIndep.comp hc).mono hs
  exact linearIndependent_iUnion_finite hi (fun i t _ ht => hind.disjoint_biSup ht)

end AMSPhysical

#print axioms AMSPhysical.coupledString_ne_zero
#print axioms AMSPhysical.joint_eigenvectors_linearIndependent

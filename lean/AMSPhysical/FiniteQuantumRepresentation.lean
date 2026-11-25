import FiniteQuantumSL2
import QuantumAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

theorem finiteQuantumK_inverse (q : K) (hq : q≠0) (l : ℕ) :
    finiteQuantumK q l*finiteQuantumKinv q l=1 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun T : Module.End K (WeightModule K) => T p.val) (quantumK_inverse q hq l)

theorem finiteQuantumKinv_inverse (q : K) (hq : q≠0) (l : ℕ) :
    finiteQuantumKinv q l*finiteQuantumK q l=1 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun T : Module.End K (WeightModule K) => T p.val) (quantumKinv_inverse q hq l)

theorem finiteQuantumK_E (q : K) (hq : q≠0) (l : ℕ) :
    finiteQuantumK q l*finiteQuantumE q l=q^2 • (finiteQuantumE q l*finiteQuantumK q l) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun T : Module.End K (WeightModule K) => T p.val) (quantumK_E q hq l)

theorem finiteQuantumK_F (q : K) (hq : q≠0) (l : ℕ) :
    finiteQuantumK q l*finiteQuantumF q l=q^(-2:ℤ) • (finiteQuantumF q l*finiteQuantumK q l) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun T : Module.End K (WeightModule K) => T p.val) (quantumK_F q hq l)

def finiteQuantumFreeRepresentation (q : K) (l : ℕ) :
    FreeAlgebra K (Fin 4) →ₐ[K] Module.End K (finiteWeightSpace (K:=K) l) :=
  FreeAlgebra.lift K ![finiteQuantumE q l,finiteQuantumF q l,finiteQuantumK q l,finiteQuantumKinv q l]

theorem finiteQuantumFree_respects (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℕ)
    {x y : FreeAlgebra K (Fin 4)} (h : QuantumSL2Relation q x y) :
    finiteQuantumFreeRepresentation q l x=finiteQuantumFreeRepresentation q l y := by
  cases h
  · simpa [finiteQuantumFreeRepresentation] using finiteQuantumK_inverse q hq l
  · simpa [finiteQuantumFreeRepresentation] using finiteQuantumKinv_inverse q hq l
  · simpa [finiteQuantumFreeRepresentation] using finiteQuantumK_E q hq l
  · simpa [finiteQuantumFreeRepresentation] using finiteQuantumK_F q hq l
  · simpa [finiteQuantumFreeRepresentation] using finiteQuantum_commutator q hq hden l

/-- Genuine finite-dimensional representation of the independently presented U_q(sl_2). -/
def finiteQuantumRepresentation (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℕ) :
    UqSL2 q →ₐ[K] Module.End K (finiteWeightSpace (K:=K) l) :=
  RingQuot.liftAlgHom K ⟨finiteQuantumFreeRepresentation q l,by
    intro x y h
    exact finiteQuantumFree_respects q hq hden l h⟩

theorem finiteQuantumRepresentation_generator (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℕ)
    (i : Fin 4) :
    finiteQuantumRepresentation q hq hden l
        (RingQuot.mkAlgHom K (QuantumSL2Relation q) (FreeAlgebra.ι K i))=
      ![finiteQuantumE q l,finiteQuantumF q l,finiteQuantumK q l,finiteQuantumKinv q l] i := by
  simp [finiteQuantumRepresentation,RingQuot.liftAlgHom_mkAlgHom_apply,finiteQuantumFreeRepresentation]

def finiteWeightVector (l : ℕ) (k : ℤ) (hk : k∈Set.Icc (0:ℤ) l) : finiteWeightSpace (K:=K) l :=
  ⟨Finsupp.single k 1,Finsupp.single_mem_supported K _ hk⟩

theorem finiteWeightSpace_finrank (l : ℕ) :
    Module.finrank K (finiteWeightSpace (K:=K) l)=l+1 := by
  let e := Finsupp.supportedEquivFinsupp (M:=K) (R:=K) (Set.Icc (0:ℤ) (l:ℤ))
  change Module.finrank K (Finsupp.supported K K (Set.Icc (0:ℤ) (l:ℤ)))=l+1
  rw [e.finrank_eq]
  simp

theorem finiteQuantum_highest_E (q : K) (l : ℕ) :
    finiteQuantumE q l (finiteWeightVector l 0 (by constructor <;> omega))=0 := by
  apply Subtype.ext
  change quantumE q (Finsupp.single 0 1)=0
  simp only [quantumE,weightShift_single,qInteger_zero,mul_zero,Finsupp.single_zero]

theorem finiteQuantum_highest_K (q : K) (l : ℕ) :
    finiteQuantumK q l (finiteWeightVector l 0 (by constructor <;> omega))=
      q^l • finiteWeightVector l 0 (by constructor <;> omega) := by
  apply Subtype.ext
  change quantumK q l (Finsupp.single 0 1)=q^l • Finsupp.single 0 1
  simp only [quantumK,weightShift_single,add_zero,mul_zero,sub_zero,zpow_natCast,
    one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]

end AMSPhysical

#print axioms AMSPhysical.finiteQuantumRepresentation
#print axioms AMSPhysical.finiteWeightSpace_finrank

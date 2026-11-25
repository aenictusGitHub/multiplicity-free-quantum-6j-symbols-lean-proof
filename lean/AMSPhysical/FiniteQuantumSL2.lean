import QuantumSL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def finiteWeightSpace (l : ℕ) : Submodule K (WeightModule K) :=
  Finsupp.supported K K (Set.Icc 0 (l:ℤ))

theorem weightShift_preserves (s : ℤ) (w : ℤ → K) (S : Set ℤ)
    (h : ∀ k∈S,w k≠0 → k+s∈S) (p : WeightModule K)
    (hp : p∈Finsupp.supported K K S) : weightShift s w p∈Finsupp.supported K K S := by
  unfold weightShift
  rw [Finsupp.lsum_apply]
  change (∑ k∈p.support,p k • Finsupp.single (k+s) (w k))∈Finsupp.supported K K S
  apply Submodule.sum_mem
  intro k hk
  by_cases hw : w k=0
  · simp only [hw,Finsupp.single_zero,smul_zero]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    exact Finsupp.single_mem_supported K _ (h k (hp hk) hw)

theorem quantumE_preserves (q : K) (l : ℕ) (p : WeightModule K)
    (hp : p∈finiteWeightSpace l) : quantumE q p∈finiteWeightSpace l := by
  apply weightShift_preserves (-1) (qInteger q) (Set.Icc 0 (l:ℤ)) _ p hp
  intro k hk hq
  rcases hk with ⟨hklo,hkhi⟩
  have hk0 : k≠0 := by intro he; rw [he,qInteger_zero] at hq; exact hq rfl
  constructor <;> omega

theorem quantumF_preserves (q : K) (l : ℕ) (p : WeightModule K)
    (hp : p∈finiteWeightSpace l) : quantumF q l p∈finiteWeightSpace l := by
  apply weightShift_preserves 1 (fun k => qInteger q ((l:ℤ)-k)) (Set.Icc 0 (l:ℤ)) _ p hp
  intro k hk hq
  change qInteger q ((l:ℤ)-k)≠0 at hq
  rcases hk with ⟨hklo,hkhi⟩
  have hkL : k≠(l:ℤ) := by intro he; rw [he,sub_self,qInteger_zero] at hq; exact hq rfl
  constructor <;> omega

theorem quantumK_preserves (q : K) (l : ℕ) (p : WeightModule K)
    (hp : p∈finiteWeightSpace l) : quantumK q l p∈finiteWeightSpace l := by
  exact weightShift_preserves 0 _ _ (by intro k hk _; simpa using hk) p hp

theorem quantumKinv_preserves (q : K) (l : ℕ) (p : WeightModule K)
    (hp : p∈finiteWeightSpace l) : quantumKinv q l p∈finiteWeightSpace l := by
  exact weightShift_preserves 0 _ _ (by intro k hk _; simpa using hk) p hp

def restrictWeightEnd (l : ℕ) (T : Module.End K (WeightModule K))
    (hT : ∀ p∈finiteWeightSpace l,T p∈finiteWeightSpace l) :
    Module.End K (finiteWeightSpace (K:=K) l) where
  toFun p := ⟨T p.val,hT p.val p.property⟩
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

def finiteQuantumE (q : K) (l : ℕ) : Module.End K (finiteWeightSpace (K:=K) l) :=
  restrictWeightEnd l (quantumE q) (quantumE_preserves q l)
def finiteQuantumF (q : K) (l : ℕ) : Module.End K (finiteWeightSpace (K:=K) l) :=
  restrictWeightEnd l (quantumF q l) (quantumF_preserves q l)
def finiteQuantumK (q : K) (l : ℕ) : Module.End K (finiteWeightSpace (K:=K) l) :=
  restrictWeightEnd l (quantumK q l) (quantumK_preserves q l)
def finiteQuantumKinv (q : K) (l : ℕ) : Module.End K (finiteWeightSpace (K:=K) l) :=
  restrictWeightEnd l (quantumKinv q l) (quantumKinv_preserves q l)

theorem finiteQuantum_commutator (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℕ) :
    finiteQuantumE q l*finiteQuantumF q l-finiteQuantumF q l*finiteQuantumE q l=
      (q-q⁻¹)⁻¹ • (finiteQuantumK q l-finiteQuantumKinv q l) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun T : Module.End K (WeightModule K) => T p.val)
    (quantum_commutator q hq hden l)

instance finiteWeightSpace_finite (l : ℕ) : Module.Finite K (finiteWeightSpace (K:=K) l) := by
  let e := Finsupp.supportedEquivFinsupp (M:=K) (R:=K) (Set.Icc (0:ℤ) (l:ℤ))
  exact Module.Finite.of_injective e.toLinearMap e.injective

end AMSPhysical

#print axioms AMSPhysical.finiteQuantum_commutator

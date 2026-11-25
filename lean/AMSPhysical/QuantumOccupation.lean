import QuantumLatticeRoots
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open Module

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Nonnegative occupation weights of a fixed total degree. -/
def occupationWeights (ι : Type*) [Fintype ι] (L : ℕ) : Set (ι → ℤ) :=
  {x | (∀ i,0≤x i) ∧ ∑ i,x i=(L:ℤ)}

theorem occupationWeight_bound (L : ℕ) (x : occupationWeights ι L) (i : ι) : x.val i≤(L:ℤ) := by
  have hh : x.val i≤∑ j,x.val j :=
    Finset.single_le_sum (fun j _ => x.property.1 j) (Finset.mem_univ i)
  rw [x.property.2] at hh
  exact hh

def occupationEncode (L : ℕ) (x : occupationWeights ι L) : ι → Fin (L+1) :=
  fun i => ⟨(x.val i).toNat,by have h₁ := x.property.1 i;have h₂ := occupationWeight_bound L x i;omega⟩

theorem occupationEncode_injective (L : ℕ) : Function.Injective (occupationEncode (ι:=ι) L) := by
  intro x y he
  apply Subtype.ext
  funext i
  have hh := congrArg (fun f : ι → Fin (L+1) => (f i).val) he
  change (x.val i).toNat=(y.val i).toNat at hh
  have hx := x.property.1 i
  have hy := y.property.1 i
  omega

instance occupationWeights_finite (L : ℕ) : Finite (occupationWeights ι L) :=
  Finite.of_injective (occupationEncode (ι:=ι) L) (occupationEncode_injective L)

instance occupationWeights_fintype (L : ℕ) : Fintype (occupationWeights ι L) := Fintype.ofFinite _

def quantumOccupationSpace (K ι : Type*) [Field K] [Fintype ι] (L : ℕ) : Submodule K (QuantumLatticeSpace K ι) :=
  Finsupp.supported K K (occupationWeights ι L)

instance quantumOccupationSpace_finite (L : ℕ) : Module.Finite K (quantumOccupationSpace K ι L) := by
  let e := Finsupp.supportedEquivFinsupp (M:=K) (R:=K) (occupationWeights ι L)
  exact Module.Finite.of_injective e.toLinearMap e.injective

def quantumOccupationBasis (L : ℕ) : Basis (occupationWeights ι L) K (quantumOccupationSpace K ι L) :=
  (Finsupp.basisSingleOne : Basis (occupationWeights ι L) K ((occupationWeights ι L) →₀ K)).map
    (Finsupp.supportedEquivFinsupp (M:=K) (R:=K) (occupationWeights ι L)).symm

@[simp] theorem quantumOccupationBasis_coe (L : ℕ) (x : occupationWeights ι L) :
    (quantumOccupationBasis (K:=K) L x).val=Finsupp.single x.val (1:K) := by
  change (((Finsupp.supportedEquivFinsupp (M:=K) (R:=K) (occupationWeights ι L)).symm
    (Finsupp.single x (1:K))) : QuantumLatticeSpace K ι)=Finsupp.single x.val (1:K)
  exact Finsupp.supportedEquivFinsupp_symm_single (M:=K) (R:=K) (occupationWeights ι L) x (1:K)

theorem occupationWeights_move (L : ℕ) (x : ι → ℤ) (hx : x∈occupationWeights ι L)
    (i j : ι) (hij : i≠j) (hj : x j≠0) : x+latticeRoot i j∈occupationWeights ι L := by
  constructor
  · intro k
    have hnonneg := hx.1 k
    by_cases hki : k=i
    · subst k
      rw [Pi.add_apply,latticeRoot_target i j hij]
      omega
    · by_cases hkj : k=j
      · subst k
        rw [Pi.add_apply,latticeRoot_source i j hij]
        omega
      · rw [Pi.add_apply,latticeRoot_other i j k hki hkj,add_zero]
        exact hnonneg
  · have hsum : (∑ k,latticeRoot i j k)=0 := by
      have he := latticePairing_root_right (fun _ : ι => (1:ℤ)) i j
      simpa only [latticePairing,one_mul,sub_self] using he
    change ∑ k,(x k+latticeRoot i j k)=(L:ℤ)
    rw [Finset.sum_add_distrib,hx.2,hsum,add_zero]

/-- Every raising/lowering root action preserves the actual finite symmetric
occupation module; the zero source coefficient handles its boundary. -/
theorem quantumLatticeMove_preserves (q : K) (L : ℕ) (i j : ι) (hij : i≠j)
    (p : QuantumLatticeSpace K ι) (hp : p∈quantumOccupationSpace K ι L) :
    quantumLatticeMove q i j p∈quantumOccupationSpace K ι L := by
  classical
  unfold quantumLatticeMove latticeShift
  rw [Finsupp.lsum_apply]
  change (∑ x∈p.support,p x • Finsupp.single (x+latticeRoot i j) (qInteger q (x j)))∈quantumOccupationSpace K ι L
  apply Submodule.sum_mem
  intro x hx
  by_cases hj : x j=0
  · simp only [hj,qInteger_zero,Finsupp.single_zero,smul_zero]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    exact Finsupp.single_mem_supported K _ (occupationWeights_move L x (hp hx) i j hij hj)

theorem quantumLatticeCartan_preserves (q : K) (L : ℕ) (h : ι → ℤ)
    (p : QuantumLatticeSpace K ι) (hp : p∈quantumOccupationSpace K ι L) :
    quantumLatticeCartan q h p∈quantumOccupationSpace K ι L := by
  classical
  unfold quantumLatticeCartan latticeShift
  rw [Finsupp.lsum_apply]
  change (∑ x∈p.support,p x • Finsupp.single (x+0) (q^(latticePairing h x)))∈quantumOccupationSpace K ι L
  apply Submodule.sum_mem
  intro x hx
  apply Submodule.smul_mem
  exact Finsupp.single_mem_supported K _ (by simpa only [add_zero] using hp hx)

end AMSPhysical

#print axioms AMSPhysical.quantumLatticeMove_preserves
#print axioms AMSPhysical.quantumOccupationSpace_finite

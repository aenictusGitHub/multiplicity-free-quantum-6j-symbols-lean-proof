import QuantumOccupation
import GaussianSeries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def occupationNatFunction (L : ℕ) (x : occupationWeights ι L) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (x.val i).toNat)

@[simp] theorem occupationNatFunction_apply (L : ℕ) (x : occupationWeights ι L) (i : ι) :
    occupationNatFunction L x i=(x.val i).toNat := by simp [occupationNatFunction]

theorem occupationNatFunction_sum (L : ℕ) (x : occupationWeights ι L) :
    (∑ i,occupationNatFunction L x i)=L := by
  have hz : ((∑ i,occupationNatFunction L x i):ℤ)=(L:ℤ) := by
    calc
      _ = ∑ i,x.val i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [occupationNatFunction_apply,Int.toNat_of_nonneg (x.property.1 i)]
      _ = (L:ℤ) := x.property.2
  exact_mod_cast hz

theorem occupationNatFunction_injective (L : ℕ) : Function.Injective (occupationNatFunction (ι:=ι) L) := by
  intro x y he
  apply Subtype.ext
  funext i
  have hh := congrArg (fun f : ι →₀ ℕ => f i) he
  simp only [occupationNatFunction_apply] at hh
  have hx := x.property.1 i
  have hy := y.property.1 i
  omega

def occupationOfNatSum (L : ℕ) (f : ι →₀ ℕ) (hf : (∑ i,f i)=L) : occupationWeights ι L :=
  ⟨fun i => (f i:ℤ),by
    constructor
    · intro i
      exact Int.natCast_nonneg _
    · rw [← Nat.cast_sum,hf]⟩

@[simp] theorem occupationNatFunction_ofNatSum (L : ℕ) (f : ι →₀ ℕ) (hf : (∑ i,f i)=L) :
    occupationNatFunction L (occupationOfNatSum L f hf)=f := by
  ext i
  simp [occupationOfNatSum]

/-- The complete occupation character is the coefficient of the literal
product of geometric series. The finite composition sum is not assumed. -/
theorem occupation_geometric_coefficient (c : ι → ℝ) (L : ℕ) :
    (∑ x : occupationWeights ι L,∏ i,c i^((x.val i).toNat))=
      PowerSeries.coeff L (∏ i,geometricSeries (c i)) := by
  classical
  rw [PowerSeries.coeff_prod]
  simp only [geometricSeries_coeff]
  apply Finset.sum_bij (fun x _ => occupationNatFunction L x)
  · intro x hx
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨occupationNatFunction_sum L x,Finset.subset_univ _⟩
  · intro x hx y hy he
    exact occupationNatFunction_injective L he
  · intro f hf
    have hh := (Finset.mem_finsuppAntidiag.mp hf).1
    exact ⟨occupationOfNatSum L f hh,Finset.mem_univ _,occupationNatFunction_ofNatSum L f hh⟩
  · intro x hx
    apply Finset.prod_congr rfl
    intro i hi
    rw [occupationNatFunction_apply]

end AMSPhysical

#print axioms AMSPhysical.occupation_geometric_coefficient

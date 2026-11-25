import OccupationPowerSeries
import QuantumTypeAFinite
import QuantumPhysicalDimension
import GaussianFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteOccupationCartan (q : ℝ) (L : ℕ) (h : ι → ℤ) : Module.End ℝ (quantumOccupationSpace ℝ ι L) :=
  restrictPreservingEnd (quantumOccupationSpace ℝ ι L)
    ⟨quantumLatticeCartan q h,quantumLatticeCartan_preserves q L h⟩

theorem finiteOccupationCartan_basis (q : ℝ) (L : ℕ) (h : ι → ℤ) (x : occupationWeights ι L) :
    finiteOccupationCartan q L h (quantumOccupationBasis (K:=ℝ) L x)=
      q^(latticePairing h x.val) • quantumOccupationBasis (K:=ℝ) L x := by
  apply Subtype.ext
  change quantumLatticeCartan q h (quantumOccupationBasis (K:=ℝ) L x).val=_
  simp only [quantumOccupationBasis_coe,quantumLatticeCartan_single,one_mul,
    Submodule.coe_smul,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem finiteOccupationCartan_trace (q : ℝ) (L : ℕ) (h : ι → ℤ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ ι L) (finiteOccupationCartan q L h)=
      ∑ x : occupationWeights ι L,q^(latticePairing h x.val) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (quantumOccupationBasis (K:=ℝ) L)]
  unfold Matrix.trace
  simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,finiteOccupationCartan_basis,map_smul,
    Module.Basis.repr_self,Finsupp.smul_apply,smul_eq_mul,Finsupp.single_eq_same,mul_one]

theorem zpow_finset_sum (q : ℝ) (hq : q≠0) (s : Finset ι) (f : ι → ℤ) :
    q^(∑ i∈s,f i)=∏ i∈s,q^(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,zpow_add₀ hq,ih]

theorem occupation_torus_product (q : ℝ) (hq : q≠0) (h : ι → ℤ) (L : ℕ) (x : occupationWeights ι L) :
    (∏ i,(q^(h i))^((x.val i).toNat))=q^(latticePairing h x.val) := by
  rw [latticePairing,zpow_finset_sum q hq]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← zpow_natCast (q^(h i)) (x.val i).toNat,← zpow_mul,
    Int.toNat_of_nonneg (x.property.1 i)]

theorem occupation_torus_character (q : ℝ) (hq : q≠0) (h : ι → ℤ) (L : ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ ι L) (finiteOccupationCartan q L h)=
      PowerSeries.coeff L (∏ i,geometricSeries (q^(h i))) := by
  rw [finiteOccupationCartan_trace,← occupation_geometric_coefficient]
  apply Finset.sum_congr rfl
  intro x hx
  exact (occupation_torus_product q hq h L x).symm

/-- The inverse-pivotal weight on the vector representation of sl_(n+1). -/
def typeAInversePivotalWeight (n : ℕ) (k : Fin (n+1)) : ℤ := -(n:ℤ)+2*(k.val:ℤ)

theorem inversePivotal_geometric_product (q : ℝ) (hq : q≠0) (n : ℕ) :
    (∏ k : Fin (n+1),geometricSeries (q^(typeAInversePivotalWeight n k)))=
      PowerSeries.rescale (q^(-(n:ℤ))) (gaussianSeries (q^2) n) := by
  unfold gaussianSeries
  rw [map_prod]
  calc
    _ = ∏ k : Fin (n+1),geometricSeries (q^(-(n:ℤ))*(q^2)^k.val) := by
      apply Finset.prod_congr rfl
      intro k hk
      congr 1
      have hEven : (q^2)^(k.val:ℤ)=q^(2*(k.val:ℤ)) := by
        rw [← zpow_natCast q 2,← zpow_mul]
        norm_num
      rw [← zpow_natCast (q^2) k.val,hEven,← zpow_add₀ hq]
      rfl
    _ = ∏ k∈Finset.range (n+1),geometricSeries (q^(-(n:ℤ))*(q^2)^k) :=
      Fin.prod_univ_eq_prod_range (fun k : ℕ => geometricSeries (q^(-(n:ℤ))*(q^2)^k)) (n+1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [geometricSeries_rescale]

/-- Closed quantum Weyl dimension expression from the actual complete
occupation basis and its torus trace, valid in every rank and degree. -/
theorem inversePivotal_trace_factorial (q : ℝ) (hq : 0<q) (n L : ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L)
      (finiteOccupationCartan q L (typeAInversePivotalWeight n))=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) := by
  rw [occupation_torus_character q (ne_of_gt hq),inversePivotal_geometric_product q (ne_of_gt hq),
    PowerSeries.coeff_rescale]
  change (q^(-(n:ℤ)))^L*gaussianCoefficient (q^2) n L=_
  rw [gaussianCoefficient_factorial q hq]
  unfold gaussianFactorial
  have hp : (q^(-(n:ℤ)))^L*q^((n*L:ℕ):ℤ)=1 := by
    rw [← zpow_natCast (q^(-(n:ℤ))) L,← zpow_mul,← zpow_add₀ (ne_of_gt hq)]
    have hz : -(n:ℤ)*(L:ℤ)+((n*L:ℕ):ℤ)=0 := by push_cast;ring
    rw [hz,zpow_zero]
  linear_combination (qfactorial q (n+L)/(qfactorial q n*qfactorial q L))*hp

end AMSPhysical

#print axioms AMSPhysical.inversePivotal_trace_factorial

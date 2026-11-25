import QuantumClebschIsometry
import QuantumCouplingNormFormula
import WeightedBasisSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def couplingBasisIndex (l m r : ℕ) (hl : r≤l) (hm : r≤m) (k : Fin (r+1)) :
    Fin (l+1) × Fin (m+1) :=
  (⟨k.val,by have hk := k.isLt;omega⟩,⟨r-k.val,by have hk := k.isLt;omega⟩)

theorem couplingBasisIndex_injective (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    Function.Injective (couplingBasisIndex l m r hl hm) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun ij : Fin (l+1) × Fin (m+1) => ij.1.val) he

theorem finiteCoupledHighest_basis (q : ℝ) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    finiteCoupledHighest q l m r hl hm=
      ∑ k : Fin (r+1),couplingCoefficient q (m:ℤ) r k.val •
        ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m))
          (couplingBasisIndex l m r hl hm k) := by
  unfold finiteCoupledHighest
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [Basis.tensorProduct_apply',standardWeightBasis_apply,standardWeightBasis_apply]
  unfold standardWeightVector couplingBasisIndex
  congr 1
  apply Subtype.ext
  change Finsupp.single ((r:ℤ)-(k.val:ℤ)) (1:ℝ)=Finsupp.single ((r-k.val:ℕ):ℤ) (1:ℝ)
  congr 1
  omega

theorem finiteCoupledHighest_norm_sum (q : ℝ) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    quantumTensorBilin q l m (finiteCoupledHighest q l m r hl hm) (finiteCoupledHighest q l m r hl hm)=
      ∑ k : Fin (r+1),(couplingCoefficient q (m:ℤ) r k.val)^2*
        quantumWeight q l k.val*quantumWeight q m (r-k.val) := by
  rw [finiteCoupledHighest_basis]
  have he := finiteWeightedPair_sum_basis
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m))
    (fun ij : Fin (l+1) × Fin (m+1) => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val)
    (couplingBasisIndex l m r hl hm) (couplingBasisIndex_injective l m r hl hm)
    (fun k : Fin (r+1) => couplingCoefficient q (m:ℤ) r k.val)
  change quantumTensorBilin q l m _ _=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro k hk
  change (quantumWeight q l k.val*quantumWeight q m (r-k.val))*(couplingCoefficient q (m:ℤ) r k.val)^2=_
  ring

theorem finiteCoupledHighest_norm_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a b r : ℕ) :
    quantumTensorBilin q (a+r) (b+r)
      (finiteCoupledHighest q (a+r) (b+r) r (by omega) (by omega))
      (finiteCoupledHighest q (a+r) (b+r) r (by omega) (by omega))=couplingNormClosed q a b r := by
  rw [finiteCoupledHighest_norm_sum]
  calc
    _=∑ k∈Finset.range (r+1),(couplingCoefficient q ((b+r:ℕ):ℤ) r k)^2*
        quantumWeight q (a+r) k*quantumWeight q (b+r) (r-k) :=
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (couplingCoefficient q ((b+r:ℕ):ℤ) r k)^2*
          quantumWeight q (a+r) k*quantumWeight q (b+r) (r-k)) (r+1)
    _=_ := by
      have he := couplingNorm_sum q hq hq1 a b r
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
      exact he

theorem finiteCoupledHighest_norm_closed_general (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    quantumTensorBilin q l m (finiteCoupledHighest q l m r hl hm) (finiteCoupledHighest q l m r hl hm)=
      couplingNormClosed q (l-r) (m-r) r := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le' hl
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le' hm
  simpa only [Nat.add_sub_cancel] using finiteCoupledHighest_norm_closed q hq hq1 a b r

/-- Closed normalization of the independently constructed finite tensor channel. -/
theorem quantumHighestNorm_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) :
    quantumHighestNorm q l m r=couplingNormClosed q (l-r.val) (m-r.val) r.val := by
  exact finiteCoupledHighest_norm_closed_general q hq hq1 l m r.val
    (channel_left_bound l m r) (channel_right_bound l m r)

end AMSPhysical

#print axioms AMSPhysical.quantumHighestNorm_closed

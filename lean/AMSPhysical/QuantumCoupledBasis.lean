import QuantumCoupledStrings
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

abbrev CoupledIndex (l m : ℕ) :=
  (r : Fin (min l m+1)) × Fin (coupledLabel l m r+1)

theorem channel_left_bound (l m : ℕ) (r : Fin (min l m+1)) : (r:ℕ)≤l :=
  (Nat.le_of_lt_succ r.isLt).trans (Nat.min_le_left l m)

theorem channel_right_bound (l m : ℕ) (r : Fin (min l m+1)) : (r:ℕ)≤m :=
  (Nat.le_of_lt_succ r.isLt).trans (Nat.min_le_right l m)

def realCoupledVector (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r+1)) :
    finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m :=
  coupledString q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m r
    (channel_left_bound l m r) (channel_right_bound l m r) k

theorem realCoupledVector_independent (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) :
    LinearIndependent ℝ (fun p : CoupledIndex l m => realCoupledVector q hq hq1 l m p.1 p.2) := by
  let ρ := finiteTensorRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m
  let c (r : Fin (min l m+1)) := quantumCasimirEigen q ((l:ℤ)+(m:ℤ)-2*(r.val:ℤ))
  let w (r : Fin (min l m+1)) (k : Fin (coupledLabel l m r+1)) := q^((l:ℤ)+(m:ℤ)-2*(r.val:ℤ)-2*(k.val:ℤ))
  have hc : Function.Injective c := by
    intro r s he
    have hr := channel_left_bound l m r
    have hr' := channel_right_bound l m r
    have hs := channel_left_bound l m s
    have hs' := channel_right_bound l m s
    have hr0 : (l:ℤ)+(m:ℤ)-2*(r.val:ℤ)∈Set.Ici (0:ℤ) := by
      change 0≤(l:ℤ)+(m:ℤ)-2*(r.val:ℤ)
      rw [← coupledLabel_cast l m r hr hr']
      exact Int.natCast_nonneg _
    have hs0 : (l:ℤ)+(m:ℤ)-2*(s.val:ℤ)∈Set.Ici (0:ℤ) := by
      change 0≤(l:ℤ)+(m:ℤ)-2*(s.val:ℤ)
      rw [← coupledLabel_cast l m s hs hs']
      exact Int.natCast_nonneg _
    have heq := quantumCasimirEigen_injective_real q hq hq1
      hr0 hs0 he
    apply Fin.ext
    omega
  have hw (r : Fin (min l m+1)) : Function.Injective (w r) := by
    intro k j he
    have hh := zpow_right_injective₀ hq hq1 he
    apply Fin.ext
    omega
  apply joint_eigenvectors_linearIndependent (ρ (uqCasimir q)) (ρ (uqGenerator q 2)) c hc w hw
    (realCoupledVector q hq hq1 l m)
  · intro r k
    exact coupledString_ne_zero q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m r (channel_left_bound l m r) (channel_right_bound l m r) k
      (Nat.le_of_lt_succ k.isLt) (fun j hj _ => ne_of_gt (qInteger_pos_real q hq hq1 j hj))
  · intro r k
    exact coupledString_Casimir q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m r (channel_left_bound l m r) (channel_right_bound l m r) k
      (fun j _ => ne_of_gt (qInteger_pos_real q hq hq1 (j+1:ℕ) (by omega)))
  · intro r k
    exact coupledString_weight q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l m r (channel_left_bound l m r) (channel_right_bound l m r) k

theorem channel_sum_integer (l m n : ℕ) :
    (∑ r∈Finset.range (n+1),((l:ℤ)+(m:ℤ)-2*(r:ℤ)+1))=
      ((n:ℤ)+1)*((l:ℤ)+(m:ℤ)+1-(n:ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

theorem coupledIndex_card (l m : ℕ) : Fintype.card (CoupledIndex l m)=(l+1)*(m+1) := by
  have he : (Fintype.card (CoupledIndex l m):ℤ)=
      (min l m+1:ℤ)*((l:ℤ)+m+1-min l m) := by
    rw [Fintype.card_sigma,Nat.cast_sum]
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    calc
      ∑ r : Fin (min l m+1),((coupledLabel l m r:ℤ)+1)=
        ∑ r : Fin (min l m+1),((l:ℤ)+(m:ℤ)-2*(r.val:ℤ)+1) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [coupledLabel_cast l m r (channel_left_bound l m r) (channel_right_bound l m r)]
      _=(∑ r∈Finset.range (min l m+1),((l:ℤ)+(m:ℤ)-2*(r:ℤ)+1)) :=
        Fin.sum_univ_eq_sum_range (fun r : ℕ => (l:ℤ)+(m:ℤ)-2*(r:ℤ)+1) (min l m+1)
      _=_ := by rw [channel_sum_integer]
  have hfinal : (Fintype.card (CoupledIndex l m):ℤ)=((l+1)*(m+1):ℕ) := by
    rw [he]
    rcases le_total l m with hlm | hml
    · rw [Nat.min_eq_left hlm]
      push_cast
      ring
    · rw [Nat.min_eq_right hml]
      push_cast
      ring
  exact_mod_cast hfinal

/-- The full actual finite quantum tensor product has a constructed coupling basis. -/
def quantumCoupledBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) :
    Basis (CoupledIndex l m) ℝ (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) := by
  letI : Nonempty (CoupledIndex l m) := ⟨⟨0,0⟩⟩
  have hcard : Fintype.card (CoupledIndex l m)=
      Module.finrank ℝ (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) := by
    rw [coupledIndex_card,Module.finrank_tensorProduct,finiteWeightSpace_finrank,finiteWeightSpace_finrank]
  exact basisOfLinearIndependentOfCardEqFinrank (K:=ℝ)
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (realCoupledVector_independent q hq hq1 l m) hcard

theorem quantumCoupledBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (p : CoupledIndex l m) : quantumCoupledBasis q hq hq1 l m p=realCoupledVector q hq hq1 l m p.1 p.2 := by
  simp [quantumCoupledBasis]

end AMSPhysical

#print axioms AMSPhysical.quantumCoupledBasis

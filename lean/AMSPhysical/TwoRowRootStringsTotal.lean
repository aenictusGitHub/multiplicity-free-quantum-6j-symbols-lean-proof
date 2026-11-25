import TwoRowRootStrings

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoRowRootStringAtTotal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m) :
    finiteWeightSpace (K:=ℝ) (S-2*r) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) := by
  subst S
  exact twoRowRootStringEmbedding q hq hq1 n hn l m ⟨r,by omega⟩

theorem twoRowRootStringAtTotal_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m) :
    twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm (standardWeightBasis (S-2*r) 0)=
      normalizedTwoRowHighest q n hn l m r hl hm := by
  subst S
  exact twoRowRootStringEmbedding_highest q hq hq1 n hn l m ⟨r,by omega⟩

theorem twoRowRootStringAtTotal_F (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m)
    (v : finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm (finiteQuantumF q (S-2*r) v)=
      typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
        (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1)
        (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v) := by
  subst S
  exact twoRowRootStringEmbedding_F q hq hq1 n hn l m ⟨r,by omega⟩ v

theorem twoRowRootStringAtTotal_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m)
    (v : finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v∈
      (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm).channel := by
  subst S
  exact twoRowRootStringEmbedding_mem_channel q hq hq1 n hn l m ⟨r,by omega⟩ v

end AMSPhysical
#print axioms AMSPhysical.twoRowRootStringAtTotal_F

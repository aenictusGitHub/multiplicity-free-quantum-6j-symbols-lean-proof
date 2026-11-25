import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 500000
namespace AMSPhysical
variable {V:Type*} [AddCommMonoid V]

/-- Exact finite support shift, including r=c and c=0. -/
theorem fin_sum_zero_below_shift (r c:ℕ) (hr:r≤c) (f:Fin (c+1) → V)
    (hzero:∀ k:Fin (c+1),k.val<r → f k=0):
    (∑ k:Fin (c+1),f k)=∑ t:Fin (c-r+1),f ⟨r+t.val,by have ht:=t.isLt;omega⟩ := by
  classical
  calc
    _=∑ k∈Finset.univ.filter (fun k:Fin (c+1)=>r≤k.val),f k:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hknot
      apply hzero
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hknot
      omega
    _=_:=by
      symm
      apply Finset.sum_bij (fun t _=>(⟨r+t.val,by have ht:=t.isLt;omega⟩:Fin (c+1)))
      · intro t ht
        simp
      · intro t ht u hu he
        apply Fin.ext
        have hh:=congrArg Fin.val he
        dsimp only at hh
        omega
      · intro k hk
        have hkr:r≤k.val:=by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hk
        refine ⟨⟨k.val-r,by have hkc:=k.isLt;omega⟩,Finset.mem_univ _,?_⟩
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      · intro t ht
        rfl

end AMSPhysical
#print axioms AMSPhysical.fin_sum_zero_below_shift

import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
variable {K V I T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem basis_sum_of_supported_injection (b : Basis I K V) (e : T → I)
    (he : Function.Injective e) (v : V) (hs : ∀ i,b.repr v i≠0 → ∃ t,e t=i) :
    v=∑ t,b.repr v (e t) • b (e t) := by
  classical
  apply b.repr.injective
  ext i
  by_cases hi : ∃ t,e t=i
  · obtain ⟨t,rfl⟩ := hi
    simp [map_sum,Finsupp.sum_apply,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_apply,he.eq_iff,eq_comm]
  · have hz : b.repr v i=0 := by by_contra hn;exact hi (hs i hn)
    have hne : ∀ t,e t≠i := fun t h => hi ⟨t,h⟩
    simp [map_sum,Finsupp.sum_apply,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_apply,hne,fun t => Ne.symm (hne t),hz]

end AMSPhysical
#print axioms AMSPhysical.basis_sum_of_supported_injection

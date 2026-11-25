import OccupationCartanLine
import AMSDynkinVertexPhase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem symmetricEndpointCartan (n : ℕ) (_hn : 0<n) (p s c : ℕ) (hs : s≤c) (i : Fin n) :
    simpleOccupationWeight n (mixedBoundaryOccupation n c (c-s) (by omega)).val i =
      mixedHighestDynkin n (p+c-s) 0 i-mixedHighestDynkin n p s i := by
  have h0 : i.succ≠(0:Fin (n+1)) := by
    simp only [ne_eq,Fin.ext_iff,Fin.val_succ,Fin.val_zero];omega
  have hL : i.castSucc≠Fin.last n := by
    simp only [ne_eq,Fin.ext_iff,Fin.coe_castSucc,Fin.val_last]
    exact ne_of_lt i.isLt
  simp only [simpleOccupationWeight,mixedBoundaryOccupation,Pi.add_apply,Pi.single_apply,
    if_neg h0,if_neg hL,if_neg (Ne.symm h0),if_neg (Ne.symm hL),
    mixedHighestDynkin,Nat.cast_zero,zero_mul,add_zero,zero_add]
  split_ifs <;> omega

end AMSPhysical
#print axioms AMSPhysical.symmetricEndpointCartan

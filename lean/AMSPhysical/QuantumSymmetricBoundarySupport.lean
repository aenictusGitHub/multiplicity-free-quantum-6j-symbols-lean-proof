import QuantumSymmetricHighestBoundary
import TwoVertexReconstruction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem symmetricHighest_boundary_support (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (y : occupationWeights (Fin (n+1)) m)
    (hc : occupationTensorCoefficients n l m v ((highestOccupation n l).val,y.val)≠0) :
    ∃ r : Fin (m+1),r.val≤l ∧ y=twoVertexOccupation n hn m r := by
  have hInterior : ∀ k : Fin (n+1),k≠0 → k≠secondVertex n hn → y.val k=0 := by
    intro k hk0 hk1
    have hv0 : k.val≠0 := fun h => hk0 (Fin.ext h)
    have hv1 : k.val≠1 := fun h => hk1 (Fin.ext h)
    let i : Fin n := ⟨k.val-1,by have hb:=k.isLt;omega⟩
    have his : i.succ=k := Fin.ext (by change k.val-1+1=k.val;omega)
    have hic : i.castSucc≠(0:Fin (n+1)) := by
      intro h
      have he:=congrArg Fin.val h
      change k.val-1=0 at he
      omega
    have hx : (highestOccupation n l).val i.castSucc=0 := by
      simp [highestOccupation,Pi.single_apply,hic,Ne.symm hic]
    by_contra hy
    have hp : 0<y.val k := by have hh:=y.property.1 k;omega
    apply hc
    apply symmetricHighest_coefficient_zero_of_excess q hq hq1 n l m v hE i
    rw [hx,his]
    exact hp
  have hy1 : y.val (secondVertex n hn)≤(l:ℤ) := by
    by_contra h
    let i : Fin n := ⟨0,hn⟩
    apply hc
    apply symmetricHighest_coefficient_zero_of_excess q hq hq1 n l m v hE i
    change (highestOccupation n l).val 0<y.val (secondVertex n hn)
    have hx : (highestOccupation n l).val 0=(l:ℤ) := by simp [highestOccupation]
    rw [hx]
    omega
  have h0:=y.property.1 (secondVertex n hn)
  have hm:=occupationWeight_bound m y (secondVertex n hn)
  refine ⟨⟨(y.val (secondVertex n hn)).toNat,by omega⟩,?_,?_⟩
  · change (y.val (secondVertex n hn)).toNat≤l
    omega
  exact occupation_twoVertex_reconstruction n hn m y hInterior

end AMSPhysical

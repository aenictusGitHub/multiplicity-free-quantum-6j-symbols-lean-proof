import QuantumMixedCoefficientRaising
import MixedBoundaryOccupation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The FULL highest boundary has exactly the expected contraction labels.
This derives the mixed fusion range from the actual generator equations. -/
theorem mixedHighest_boundary_support (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (y : occupationWeights (Fin (n+1)) m)
    (hc : occupationTensorCoefficients n l m v ((highestOccupation n l).val,y.val)≠0) :
    ∃ (r : ℕ) (_hrl : r≤l) (hrm : r≤m),y=mixedBoundaryOccupation n m r hrm := by
  have hInterior : ∀ k : Fin (n+1),k≠0 → k≠Fin.last n → y.val k=0 := by
    intro k hk0 hkn
    have hkn' : k.val<n := by
      have hb := k.isLt
      by_contra h
      have he : k=Fin.last n := Fin.ext (by simp only [Fin.val_last];omega)
      exact hkn he
    let i : Fin n := ⟨k.val,hkn'⟩
    have hik : i.castSucc=k := Fin.ext rfl
    have hx : (highestOccupation n l).val i.castSucc=0 := by
      rw [hik]
      simp [highestOccupation,Pi.single_apply,hk0,Ne.symm hk0]
    by_contra hy
    have hp : 0<y.val k := by have hh:=y.property.1 k;omega
    apply hc
    apply mixedHighest_coefficient_zero_of_excess q hq hq1 n l m v hE i
    rw [hx,hik]
    exact hp
  have hy0 : y.val 0≤(l:ℤ) := by
    by_contra h
    let i : Fin n := ⟨0,hn⟩
    have hi : i.castSucc=(0:Fin (n+1)) := Fin.ext rfl
    apply hc
    apply mixedHighest_coefficient_zero_of_excess q hq hq1 n l m v hE i
    rw [hi]
    have hx : (highestOccupation n l).val 0=(l:ℤ) := by simp [highestOccupation]
    rw [hx]
    omega
  have h0 := y.property.1 0
  have hm := occupationWeight_bound m y 0
  refine ⟨(y.val 0).toNat,by omega,by omega,?_⟩
  exact occupation_endpoints_reconstruction n m hn y hInterior

end AMSPhysical

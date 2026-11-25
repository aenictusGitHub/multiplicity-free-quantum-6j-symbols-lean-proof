import SymmetricHighestCoordinates
import QuantumPositive
import QuantumOccupationEnergy

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- All symmetric/symmetric highest coefficients are determined by the first-factor
highest boundary. The proof uses decreasing first occupation height and
the actual nonzero raising coefficients, with no decomposition hypothesis. -/
theorem pairSymmetricHighest_zero_of_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (f : OccupationPairLattice n →₀ ℝ)
    (hSupport : ∀ x y,f (x,y)≠0 → x∈occupationWeights (Fin (n+1)) L)
    (hE : ∀ i : Fin n,pairSymmetricRaising q n i f=0)
    (hBoundary : ∀ y,f ((highestOccupation n L).val,y)=0) : f=0 := by
  have aux : ∀ k : ℕ,∀ x : occupationWeights (Fin (n+1)) L,
      occupationHeight n L x=k → ∀ y : Fin (n+1) → ℤ,f (x.val,y)=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hk y
      by_cases hx : x=highestOccupation n L
      · rw [hx]
        exact hBoundary y
      · obtain ⟨i,hi⟩ := occupation_nonhighest_donor n L x hx
        let z := raisedOccupation n L x i hi
        have hz : occupationHeight n L z<k := by
          have hh := raisedOccupation_height n L x i hi
          change occupationHeight n L z+1=occupationHeight n L x at hh
          omega
        have hlow := ih (occupationHeight n L z) hz z rfl (y-latticeRoot i.castSucc i.succ)
        have he := pairSymmetricRaising_zero_coordinate q n i f (hE i) z.val y
        have hxz : z.val-latticeRoot i.castSucc i.succ=x.val := by
          change x.val+latticeRoot i.castSucc i.succ-latticeRoot i.castSucc i.succ=x.val
          abel
        have hj : z.val i.succ+1=x.val i.succ := by
          dsimp only [z]
          rw [raisedOccupation_source]
          ring
        rw [hxz,hj,hlow,zero_mul,add_zero] at he
        have hmul := (mul_eq_zero.mp he).resolve_right (zpow_ne_zero _ (ne_of_gt hq))
        exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt (qInteger_pos_real q hq hq1 _ hi))
  ext p
  rcases p with ⟨x,y⟩
  by_cases hx : x∈occupationWeights (Fin (n+1)) L
  · exact aux (occupationHeight n L ⟨x,hx⟩) ⟨x,hx⟩ rfl y
  · by_contra h
    apply hx
    apply hSupport x y
    simpa only [Finsupp.zero_apply] using h

end AMSPhysical

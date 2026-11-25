import QuantumPairRaising
import QuantumPositive

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

/-- Every boundary equation is used: a mixed highest coefficient must have
y_i <= x_i at every nonterminal coordinate. No dominance or fusion rule is
assumed. This follows by induction to the genuine negative-occupation edge. -/
theorem pairHighest_zero_of_excess (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ)
    (i : Fin n) (f : OccupationPairLattice n →₀ ℝ)
    (hSupport : ∀ x y,f (x,y)≠0 → 0≤x i.castSucc)
    (hE : pairLatticeRaising q n i f=0)
    (x y : Fin (n+1) → ℤ) (hExcess : x i.castSucc<y i.castSucc) : f (x,y)=0 := by
  have aux : ∀ k : ℕ,∀ x y : Fin (n+1) → ℤ,
      0≤x i.castSucc → (x i.castSucc).toNat=k → x i.castSucc<y i.castSucc → f (x,y)=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x y hx hk hxy
      let d := latticeRoot i.castSucc i.succ
      have hdx : (x-d) i.castSucc=x i.castSucc-1 := by
        dsimp only [d]
        rw [Pi.sub_apply,latticeRoot_target _ _ (typeA_root_endpoints n i)]
      have hdy : (y-d) i.castSucc=y i.castSucc-1 := by
        dsimp only [d]
        rw [Pi.sub_apply,latticeRoot_target _ _ (typeA_root_endpoints n i)]
      have hpre : f (x-d,y-d)=0 := by
        by_cases hz : x i.castSucc=0
        · by_contra hn
          have hh := hSupport (x-d) (y-d) hn
          omega
        · have hp : 0<x i.castSucc := by omega
          apply ih ((x-d) i.castSucc).toNat (by omega) (x-d) (y-d) (by omega) rfl
          omega
      have he := pairLatticeRaising_zero_coordinate q n i f hE x (y-d)
      change f (x-d,y-d)*qInteger q (x i.succ+1)*q^(-simpleOccupationWeight n (y-d) i)+
        f (x,y-d+d)*qInteger q ((y-d) i.castSucc+1)=0 at he
      rw [hpre,zero_mul,zero_mul,zero_add,sub_add_cancel] at he
      have hyi : (y-d) i.castSucc+1=y i.castSucc := by omega
      rw [hyi] at he
      exact (mul_eq_zero.mp he).resolve_right (ne_of_gt (qInteger_pos_real q hq hq1 _ (by omega)))
  by_cases hx : 0≤x i.castSucc
  · exact aux (x i.castSucc).toNat x y hx rfl hExcess
  · by_contra h
    exact hx (hSupport x y h)

end AMSPhysical

import PureMixedCarrierBoundary
import OppositeCartanLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem amsActualBoundary_pure_symmetric_mixed (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (p : ℕ) (v : (actualMixedCarrier q hq hq1 n (by omega) p 0).space) :
    amsActualBoundary q hq hq1 n hn (actualMixedCarrier q hq hq1 n (by omega) p 0).irrep
      ((actualMixedCarrier q hq hq1 n (by omega) p 0).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualMixedCarrier q hq hq1 n (by omega) p 0).irrep) v)=
      occupationAugmentation n p ((actualMixedCarrier q hq hq1 n (by omega) p 0).mapTo (ne_of_gt hq)
        (actualSymmetricCarrier q hq hq1 n p) v) := by
  let M:=actualMixedCarrier q hq hq1 n (by omega) p 0
  let S:=actualSymmetricCarrier q hq hq1 n p
  have he:=congrArg (fun F=>amsActualBoundary q hq hq1 n hn M.irrep (F v))
    (M.mapTo_comp (ne_of_gt hq) S (fixedActualCarrier M.irrep))
  dsimp only [LinearMap.comp_apply] at he
  exact he.symm.trans (amsActualBoundary_symmetric q hq hq1 n hn p (M.mapTo (ne_of_gt hq) S v))

theorem amsActualBoundary_pure_opposite_mixed (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (s : ℕ) (v : (actualMixedCarrier q hq hq1 n (by omega) 0 s).space) :
    amsActualBoundary q hq hq1 n hn (actualMixedCarrier q hq hq1 n (by omega) 0 s).irrep
      ((actualMixedCarrier q hq hq1 n (by omega) 0 s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualMixedCarrier q hq hq1 n (by omega) 0 s).irrep) v)=
      occupationAugmentation n s ((actualMixedCarrier q hq hq1 n (by omega) 0 s).mapTo (ne_of_gt hq)
        (actualOppositeCarrier q hq hq1 n (by omega) s) v) := by
  let M:=actualMixedCarrier q hq hq1 n (by omega) 0 s
  let O:=actualOppositeCarrier q hq hq1 n (by omega) s
  have he:=congrArg (fun F=>amsActualBoundary q hq hq1 n hn M.irrep (F v))
    (M.mapTo_comp (ne_of_gt hq) O (fixedActualCarrier M.irrep))
  dsimp only [LinearMap.comp_apply] at he
  exact he.symm.trans (amsActualBoundary_opposite q hq hq1 n hn s (M.mapTo (ne_of_gt hq) O v))

/-- On the Cartan weight selected by a symmetric first leg, the single
actual boundary agrees with the mixed all-first boundary. This also proves
the pure-symmetric and pure-opposite alias cases. -/
theorem amsActualBoundary_mixed_projected_Cartan (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (a p s d : ℕ) (hbal : a+p=s+d)
    (v : (actualMixedCarrier q hq hq1 n (by omega) p s).space)
    (hV : ∀ i : Fin n,(actualMixedCarrier q hq hq1 n (by omega) p s).frame.action
      (typeAAlgebraGenerator q n i 2) v =
      q^(mixedHighestDynkin n d 0 i-mixedHighestDynkin n a 0 i) • v) :
    amsActualBoundary q hq hq1 n hn (actualMixedCarrier q hq hq1 n (by omega) p s).irrep
      ((actualMixedCarrier q hq hq1 n (by omega) p s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualMixedCarrier q hq hq1 n (by omega) p s).irrep) v)=
      mixedFirstBoundaryFunctional n p s v.val := by
  by_cases hs : s=0
  · subst s
    rw [amsActualBoundary_pure_symmetric_mixed]
    let M:=actualMixedCarrier q hq hq1 n (by omega) p 0
    let S:=actualSymmetricCarrier q hq hq1 n p
    have hK : ∀ i : Fin n,typeAFiniteGenerator q (ne_of_gt hq)
        (qInteger_denominator_ne_zero q hq hq1) n p i 2 (M.mapTo (ne_of_gt hq) S v)=
        q^(simpleOccupationWeight n (highestOccupation n p).val i) • M.mapTo (ne_of_gt hq) S v := by
      intro i
      have he:=M.mapTo_intertwines (ne_of_gt hq) S (typeAAlgebraGenerator q n i 2) v
      rw [hV i,map_smul] at he
      have hExp : mixedHighestDynkin n d 0 i-mixedHighestDynkin n a 0 i=
          simpleOccupationWeight n (highestOccupation n p).val i := by
        rw [simpleOccupationWeight_highest]
        simp only [mixedHighestDynkin,Nat.cast_zero,zero_mul,add_zero]
        split_ifs <;> omega
      rw [hExp] at he
      exact he.symm
    exact (occupationAugmentation_joint_cartan q hq hq1 n p (highestOccupation n p) _ hK).trans
      (actualPureMixed_symmetric_boundary q hq hq1 n (by omega) p v).symm
  · by_cases hp : p=0
    · subst p
      rw [amsActualBoundary_pure_opposite_mixed]
      let M:=actualMixedCarrier q hq hq1 n (by omega) 0 s
      let O:=actualOppositeCarrier q hq hq1 n (by omega) s
      have hK : ∀ i : Fin n,typeAOppositeSymmetricRepresentation q (ne_of_gt hq)
          (qInteger_denominator_ne_zero q hq hq1) n s (typeAAlgebraGenerator q n i 2) (M.mapTo (ne_of_gt hq) O v)=
          q^(-simpleOccupationWeight n (highestOccupation n s).val i) • M.mapTo (ne_of_gt hq) O v := by
        intro i
        have he:=M.mapTo_intertwines (ne_of_gt hq) O (typeAAlgebraGenerator q n i 2) v
        rw [hV i,map_smul] at he
        have hExp : mixedHighestDynkin n d 0 i-mixedHighestDynkin n a 0 i=
            -simpleOccupationWeight n (highestOccupation n s).val i := by
          rw [simpleOccupationWeight_highest]
          simp only [mixedHighestDynkin,Nat.cast_zero,zero_mul,add_zero]
          split_ifs <;> omega
        rw [hExp] at he
        exact he.symm
      exact (occupationAugmentation_opposite_cartan q hq hq1 n s (highestOccupation n s) _ hK).trans
        (actualPureMixed_opposite_boundary q hq hq1 n (by omega) s v).symm
    · exact amsActualBoundary_mixed_positive_parameters q hq hq1 n hn p s (by omega) (by omega) v

end AMSPhysical
#print axioms AMSPhysical.amsActualBoundary_mixed_projected_Cartan

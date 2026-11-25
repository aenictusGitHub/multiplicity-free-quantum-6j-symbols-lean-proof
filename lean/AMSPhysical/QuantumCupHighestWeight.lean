import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical

theorem mixedHighestDynkin_shifted_rank (n d h : ℕ) (hRank : h=0 ∨ n=1) :
    mixedHighestDynkin n (d+h) 0=mixedHighestDynkin n d h := by
  funext i
  rcases hRank with hh|hh
  · subst h
    rfl
  · subst n
    have hi : i=0 := Fin.eq_zero i
    subst i
    simp [mixedHighestDynkin,Nat.cast_add]

theorem physicalQuantumCupSpan_le_symmetric_highest (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m h c : ℕ) (hRank : h=0 ∨ n=1) :
    physicalQuantumCupSpan q n l m h c ≤ typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q hq hD n l (m+h) c) (mixedHighestDynkin n (l+c-m+h) 0) := by
  rw [mixedHighestDynkin_shifted_rank n (l+c-m) h hRank]
  exact physicalQuantumCupSpan_le_highest q hq hD n l m h c

end AMSPhysical

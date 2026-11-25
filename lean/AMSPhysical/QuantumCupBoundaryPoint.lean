import QuantumCupMonomial
import QuantumTriplePositiveSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupBoundaryPoint (n : ℕ) (l h c : ℤ) (t k : ℕ) : OccupationTripleLattice n :=
  (Pi.single 0 l,Pi.single 0 (t:ℤ)+Pi.single (Fin.last n) (h+(k:ℤ)),
    Pi.single 0 (c-(k:ℤ))+Pi.single (Fin.last n) (k:ℤ))

theorem tripleLeftCreation_thirdLower_support (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (fun p =>a ≤ p.2.2 0) f) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>a ≤ p.2.2 0) (tripleLeftCreation q n f) := by
  unfold tripleLeftCreation
  rw [LinearMap.sum_apply]
  apply coefficientSupported_sum
  intro j
  apply coefficientSupported_weightedTranslation _ _ _ _ f hf
  intro p hp
  simpa only [tripleLeftCreationShift,Prod.snd_add,add_zero] using hp

theorem tripleRightCreation_thirdLower_support (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (fun p =>a ≤ p.2.2 0) f) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>a ≤ p.2.2 0) (tripleRightCreation q n f) := by
  unfold tripleRightCreation
  rw [LinearMap.sum_apply]
  apply coefficientSupported_sum
  intro j
  apply coefficientSupported_weightedTranslation _ _ _ _ f hf
  intro p hp
  simp only [tripleRightCreationShift,Prod.snd_add,Pi.add_apply,Pi.single_apply]
  split_ifs <;> omega

theorem quantumCupMonomial_thirdLower_support (q : ℝ) (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>c-(k:ℤ) ≤ p.2.2 0)
      (quantumCupMonomial q n l h c t k) := by
  apply coefficientSupported_pow _ _ (tripleLeftCreation_thirdLower_support q n (c-(k:ℤ)))
  apply coefficientSupported_pow _ _ (tripleRightCreation_thirdLower_support q n (c-(k:ℤ)))
  apply coefficientSupported_single
  simp only [Pi.single_eq_same,le_refl]

/-- A literal triangular boundary, derived from monotone occupation support. -/
theorem quantumCupBoundary_above_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l h c : ℤ)
    (t k t' k' : ℕ) (hk : k < k') :
    quantumCupMonomial q n l h c t k (quantumCupBoundaryPoint n l h c t' k')=0 := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hh;omega
  by_contra hc
  have h0:=quantumCupMonomial_thirdLower_support q n l h c t k _ hc
  simp only [quantumCupBoundaryPoint,Pi.add_apply,Pi.single_eq_same,Pi.single_apply,
    if_neg (Ne.symm hn0),add_zero] at h0
  omega

end AMSPhysical

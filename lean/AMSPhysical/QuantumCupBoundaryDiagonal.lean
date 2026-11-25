import QuantumCupBoundaryPoint
import QuantumTripleBoundaryPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

/-- The diagonal boundary coefficient is evaluated by two independently
proved one-path occupation recurrences, with no Racah identification. -/
theorem quantumCupBoundary_diagonal (q : ℝ) (hq : q≠0) (n : ℕ) (hn : 0<n)
    (l h c : ℤ) (t k : ℕ) (hl : (t:ℤ) ≤ l) (hh : 0 ≤ h) (hc : (k:ℤ) ≤ c) :
    quantumCupMonomial q n l h c t k (quantumCupBoundaryPoint n l h c t k)=
      q^((t:ℤ)*(1-l)-h*(k:ℤ)-(k:ℤ)^2+(k:ℤ)) := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hs:=congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hs;omega
  have hf:=tripleCupBase_nonnegative_support n (l-(t:ℤ)) h (c-(k:ℤ)) (by omega) hh (by omega)
  have hRight:=tripleRightCreation_power_middle_boundary q hq n h
    (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))) hf (Pi.single 0 (l-(t:ℤ))) (Pi.single 0 (c-(k:ℤ))) k
  have hz : (Pi.single 0 (c-(k:ℤ)) : Fin (n+1) → ℤ) (Fin.last n)=0 := by simp [Pi.single_apply,hn0]
  rw [hz,add_zero,show tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))
    (Pi.single 0 (l-(t:ℤ)),Pi.single (Fin.last n) h,Pi.single 0 (c-(k:ℤ)))=1 by simp [tripleCupBase],mul_one] at hRight
  have hLeft:=tripleLeftCreation_power_first_boundary q hq n (l-(t:ℤ))
    (((tripleRightCreation q n)^k) (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))))
    (coefficientSupported_pow (tripleOccupationNonnegative n) (tripleRightCreation q n)
      (tripleRightCreation_nonnegative_support q n) _ hf k)
    (Pi.single (Fin.last n) (h+(k:ℤ))) (Pi.single 0 (c-(k:ℤ))+Pi.single (Fin.last n) (k:ℤ)) t
  have hy : (Pi.single (Fin.last n) (h+(k:ℤ)) : Fin (n+1) → ℤ) 0=0 := by simp [Pi.single_apply,Ne.symm hn0]
  rw [hy,add_zero,hRight] at hLeft
  have hp : ((Pi.single 0 (l-(t:ℤ)+(t:ℤ)),Pi.single (Fin.last n) (h+(k:ℤ))+Pi.single 0 (t:ℤ),
      Pi.single 0 (c-(k:ℤ))+Pi.single (Fin.last n) (k:ℤ)) : OccupationTripleLattice n)=
      quantumCupBoundaryPoint n l h c t k := by
    ext i <;> simp [quantumCupBoundaryPoint,Pi.single_apply] <;> split_ifs <;> ring
  rw [hp] at hLeft
  change quantumCupMonomial q n l h c t k (quantumCupBoundaryPoint n l h c t k)=_ at hLeft
  rw [← zpow_add₀ hq] at hLeft
  have he : -(l-(t:ℤ))*(t:ℤ)-(t:ℤ)^2+(t:ℤ)+(-h*(k:ℤ)-(k:ℤ)^2+(k:ℤ))=
      (t:ℤ)*(1-l)-h*(k:ℤ)-(k:ℤ)^2+(k:ℤ) := by ring
  rw [he] at hLeft
  exact hLeft

theorem quantumCupBoundary_diagonal_pos (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l h c : ℤ) (t k : ℕ) (hl : (t:ℤ) ≤ l) (hh : 0 ≤ h) (hc : (k:ℤ) ≤ c) :
    0<quantumCupMonomial q n l h c t k (quantumCupBoundaryPoint n l h c t k) := by
  rw [quantumCupBoundary_diagonal q (ne_of_gt hq) n hn l h c t k hl hh hc]
  exact zpow_pos hq _

end AMSPhysical
#print axioms AMSPhysical.quantumCupBoundary_diagonal

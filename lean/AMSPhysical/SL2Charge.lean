import InvariantSL2
import PolynomialWeight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def vectorCovectorWeight : Fin 8 → ℤ := ![1,1,1,1,-1,-1,-1,-1]

def IsSL2Invariant (p : P8 K) : Prop :=
  ∀ a b c d, det2 a b c d=1 → ∀ v, eval (twoAction a b c d v) p=eval v p

theorem normalized_det (a b c d t : K) (ht : t≠0)
    (hs : t^2=det2 a b c d) : det2 (a/t) (b/t) (c/t) (d/t)=1 := by
  unfold det2 at *
  field_simp [ht]
  linear_combination -hs

theorem twoAction_normalize (a b c d t : K) (ht : t≠0)
    (hs : t^2=det2 a b c d) (v : Fin 8 → K) :
    twoAction a b c d v=
      weightScale vectorCovectorWeight t (twoAction (a/t) (b/t) (c/t) (d/t) v) := by
  have hd := normalized_det a b c d t ht hs
  have hD : det2 a b c d≠0 := by rw [← hs]; exact pow_ne_zero 2 ht
  funext i
  fin_cases i <;> simp [twoAction,weightScale,vectorCovectorWeight,hd]
  all_goals field_simp [ht,hD]
  all_goals rw [← hs]

theorem sl2_charge_relativeI [IsAlgClosed K] (h : ℕ) (p : P8 K)
    (hp : IsSL2Invariant p)
    (hw : HasPolynomialWeight vectorCovectorWeight (-(2*(h:ℤ))) p) :
    IsRelativeInvariantI h p := by
  intro a b c d hD v
  obtain ⟨t,hts⟩ := IsAlgClosed.exists_pow_nat_eq (det2 a b c d) (by norm_num : 0<2)
  have ht : t≠0 := by intro hz; rw [hz] at hts; simp at hts; exact hD hts.symm
  rw [twoAction_normalize a b c d t ht hts,eval_weightScale _ _ _ hw t ht]
  rw [hp (a/t) (b/t) (c/t) (d/t) (normalized_det a b c d t ht hts)]
  rw [← hts,← pow_mul]
  have he : ((2*h:ℕ):ℤ)=2*(h:ℤ) := by omega
  rw [← he,zpow_neg,zpow_natCast]
  field_simp

theorem sl2_charge_relativeII [IsAlgClosed K] (h : ℕ) (p : P8 K)
    (hp : IsSL2Invariant p)
    (hw : HasPolynomialWeight vectorCovectorWeight (2*(h:ℤ)) p) :
    IsRelativeInvariantII h p := by
  intro a b c d hD v
  obtain ⟨t,hts⟩ := IsAlgClosed.exists_pow_nat_eq (det2 a b c d) (by norm_num : 0<2)
  have ht : t≠0 := by intro hz; rw [hz] at hts; simp at hts; exact hD hts.symm
  rw [twoAction_normalize a b c d t ht hts,eval_weightScale _ _ _ hw t ht]
  rw [hp (a/t) (b/t) (c/t) (d/t) (normalized_det a b c d t ht hts)]
  rw [← hts,← pow_mul]
  congr 1
  norm_cast

theorem sl2_typeI_surjective [Infinite K] [IsAlgClosed K] (h : ℕ) (p : P8 K)
    (hp : IsSL2Invariant p)
    (hw : HasPolynomialWeight vectorCovectorWeight (-(2*(h:ℤ))) p) :
    ∃ f : P4 K, p=shiftI h f :=
  ⟨covBack p,relativeInvariantI_reconstruction h p (sl2_charge_relativeI h p hp hw)⟩

theorem sl2_typeII_surjective [Infinite K] [IsAlgClosed K] (h : ℕ) (p : P8 K)
    (hp : IsSL2Invariant p)
    (hw : HasPolynomialWeight vectorCovectorWeight (2*(h:ℤ)) p) :
    ∃ f : P4 K, p=shiftII h f :=
  ⟨evalBack p,relativeInvariantII_reconstruction h p (sl2_charge_relativeII h p hp hw)⟩

end AMSPhysical

#print axioms AMSPhysical.sl2_typeI_surjective
#print axioms AMSPhysical.sl2_typeII_surjective

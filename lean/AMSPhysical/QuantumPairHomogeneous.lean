import QuantumMixedOscillator
import GradedWeightedTranslation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def occupationPairDegree (n : ℕ) : OccupationPairLattice n →+ ℤ where
  toFun p := (∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2 i)
  map_zero' := by simp
  map_add' p z := by
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Finset.sum_add_distrib]
    ring

theorem occupationPairDegree_creation_shift (n : ℕ) (i : Fin (n+1)) :
    occupationPairDegree n (mixedCreationShift n i)=2 := by
  simp [occupationPairDegree,mixedCreationShift,Pi.single_apply]

theorem pairLatticeCreation_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationPairLattice n →₀ ℝ) (hf : CoefficientHomogeneous (occupationPairDegree n) a f) :
    CoefficientHomogeneous (occupationPairDegree n) (a+2) (pairLatticeCreation q n f) := by
  unfold pairLatticeCreation
  rw [LinearMap.sum_apply]
  apply coefficientHomogeneous_sum
  intro i
  have h:=coefficientHomogeneous_weightedTranslation (occupationPairDegree n) a f hf
    (mixedCreationShift n i) (mixedCreationCoefficient q n i)
  simpa only [occupationPairDegree_creation_shift] using h

theorem pairLatticeCreation_pow_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationPairLattice n →₀ ℝ) (hf : CoefficientHomogeneous (occupationPairDegree n) a f)
    (t : ℕ) :
    CoefficientHomogeneous (occupationPairDegree n) (a+2*(t:ℤ)) (((pairLatticeCreation q n)^t) f) := by
  induction t with
  | zero => simpa only [Nat.cast_zero,mul_zero,add_zero,pow_zero,Module.End.one_apply] using hf
  | succ t ih =>
    have h:=pairLatticeCreation_homogeneous q n (a+2*(t:ℤ)) _ ih
    rw [show a+2*((t+1:ℕ):ℤ)=a+2*(t:ℤ)+2 by push_cast;ring,pow_succ',Module.End.mul_apply]
    exact h

/-- The exact physical radial oscillator relation on any fixed total degree. -/
theorem pairLatticeAnnihilation_creation_homogeneous (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (a : ℤ) (f : OccupationPairLattice n →₀ ℝ)
    (hf : CoefficientHomogeneous (occupationPairDegree n) a f) :
    pairLatticeAnnihilation q n (pairLatticeCreation q n f)=
      q^(-2:ℤ) • pairLatticeCreation q n (pairLatticeAnnihilation q n f)+
        (q^(-a-(n:ℤ))*qInteger q (a+(n:ℤ)+1)) • f := by
  have h:=congrArg (fun T : Module.End ℝ (OccupationPairLattice n →₀ ℝ) =>T f)
    (pairLatticeAnnihilation_creation_commutator q hq hD n)
  change pairLatticeAnnihilation q n (pairLatticeCreation q n f)-
    q^(-2:ℤ) • pairLatticeCreation q n (pairLatticeAnnihilation q n f)=_ at h
  have he : (fun p : OccupationPairLattice n =>
      q^(-(∑ i : Fin (n+1),p.1 i)-(∑ i : Fin (n+1),p.2 i)-(n:ℤ))*
        qInteger q ((∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2 i)+(n:ℤ)+1))=
      (fun p =>q^(-occupationPairDegree n p-(n:ℤ))*qInteger q (occupationPairDegree n p+(n:ℤ)+1)) := by
    funext p
    simp only [occupationPairDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
    congr 2
    ring
  rw [he] at h
  dsimp only at h
  rw [weightedTranslation_zero_homogeneous (occupationPairDegree n) a f hf
    (fun z : ℤ =>q^(-z-(n:ℤ))*qInteger q (z+(n:ℤ)+1))] at h
  exact (sub_eq_iff_eq_add).mp h |>.trans (add_comm _ _)

end AMSPhysical

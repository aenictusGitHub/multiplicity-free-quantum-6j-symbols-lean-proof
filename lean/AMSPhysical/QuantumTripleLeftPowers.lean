import QuantumTripleLeftOscillator
import GradedCreationPowers
import GradedOscillatorPowers
import QuantumOscillatorLadderScalar
import QuantumTripleCupBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLeftDegree_left_shift (n : ℕ) (i : Fin (n+1)) :
    tripleLeftDegree n (tripleLeftCreationShift n i)=2 := by
  simp [tripleLeftDegree,tripleLeftCreationShift,Pi.single_apply]

theorem tripleLeftDegree_right_shift (n : ℕ) (i : Fin (n+1)) :
    tripleLeftDegree n (tripleRightCreationShift n i)=1 := by
  simp [tripleLeftDegree,tripleRightCreationShift,Pi.single_apply]

theorem tripleLeftCreation_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleLeftDegree n) a f) :
    CoefficientHomogeneous (tripleLeftDegree n) (a+2) (tripleLeftCreation q n f) :=
  sumWeightedTranslation_homogeneous (tripleLeftDegree n) (tripleLeftCreationShift n)
    (tripleLeftCreationCoefficient q n) 2 (tripleLeftDegree_left_shift n) a f hf

theorem tripleRightCreation_left_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleLeftDegree n) a f) :
    CoefficientHomogeneous (tripleLeftDegree n) (a+1) (tripleRightCreation q n f) :=
  sumWeightedTranslation_homogeneous (tripleLeftDegree n) (tripleRightCreationShift n)
    (tripleRightCreationCoefficient q n) 1 (tripleLeftDegree_right_shift n) a f hf

theorem tripleLeftCreation_pow_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleLeftDegree n) a f) (t : ℕ) :
    CoefficientHomogeneous (tripleLeftDegree n) (a+2*(t:ℤ)) (((tripleLeftCreation q n)^t) f) :=
  gradedCreation_pow (tripleLeftDegree n) (tripleLeftCreation q n) 2 (tripleLeftCreation_homogeneous q n) a f hf t

theorem tripleRightCreation_pow_left_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleLeftDegree n) a f) (t : ℕ) :
    CoefficientHomogeneous (tripleLeftDegree n) (a+(t:ℤ)) (((tripleRightCreation q n)^t) f) := by
  simpa only [one_mul] using gradedCreation_pow (tripleLeftDegree n) (tripleRightCreation q n) 1
    (tripleRightCreation_left_homogeneous q n) a f hf t

theorem tripleCupBase_left_homogeneous (n : ℕ) (l h c : ℤ) :
    CoefficientHomogeneous (tripleLeftDegree n) (l+h) (tripleCupBase n l h c) := by
  have h0:=coefficientHomogeneous_single (tripleLeftDegree n)
    (Pi.single 0 l,Pi.single (Fin.last n) h,Pi.single 0 c) 1
  simpa only [tripleCupBase,tripleLeftDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Pi.single_apply,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h0

theorem tripleLeftAnnihilation_creation_homogeneous (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (a : ℤ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : CoefficientHomogeneous (tripleLeftDegree n) a f) :
    tripleLeftAnnihilation q n (tripleLeftCreation q n f)=
      q^(-2:ℤ) • tripleLeftCreation q n (tripleLeftAnnihilation q n f)+
        (q^(-a-(n:ℤ))*qInteger q (a+(n:ℤ)+1)) • f := by
  have h:=DFunLike.congr_fun (tripleLeftAnnihilation_creation_commutator q hq hD n) f
  change tripleLeftAnnihilation q n (tripleLeftCreation q n f)-
    q^(-2:ℤ) • tripleLeftCreation q n (tripleLeftAnnihilation q n f)=_ at h
  rw [weightedTranslation_zero_homogeneous (tripleLeftDegree n) a f hf
    (fun z : ℤ =>q^(-z-(n:ℤ))*qInteger q (z+(n:ℤ)+1))] at h
  exact (sub_eq_iff_eq_add).mp h |>.trans (add_comm _ _)

theorem tripleLeftAnnihilation_creation_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (a : ℤ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : CoefficientHomogeneous (tripleLeftDegree n) a f) (t : ℕ) :
    tripleLeftAnnihilation q n (((tripleLeftCreation q n)^(t+1)) f)=
      (q^(-2:ℤ))^(t+1) • ((tripleLeftCreation q n)^(t+1)) (tripleLeftAnnihilation q n f)+
        quantumOscillatorLadderCoefficient q (a+(n:ℤ)) (t+1) • ((tripleLeftCreation q n)^t) f := by
  apply gradedOscillator_power (tripleLeftCreation q n) (tripleLeftAnnihilation q n) (q^(-2:ℤ))
    (quantumOscillatorLadderCoefficient q (a+(n:ℤ)))
    (fun s =>q^(-(a+(n:ℤ))-2*(s:ℤ))*qInteger q (a+(n:ℤ)+2*(s:ℤ)+1))
    (quantumOscillatorLadderCoefficient_zero q (a+(n:ℤ)))
    (quantumOscillatorLadderCoefficient_succ q hq hD (a+(n:ℤ))) f
  intro s
  have h:=tripleLeftAnnihilation_creation_homogeneous q hq hD n (a+2*(s:ℤ))
    (((tripleLeftCreation q n)^s) f) (tripleLeftCreation_pow_homogeneous q n a f hf s)
  have he : -(a+2*(s:ℤ))-(n:ℤ)= -(a+(n:ℤ))-2*(s:ℤ) := by ring
  have he' : a+2*(s:ℤ)+(n:ℤ)+1=a+(n:ℤ)+2*(s:ℤ)+1 := by ring
  rw [he,he'] at h
  simpa only [pow_succ',Module.End.mul_apply] using h

end AMSPhysical

import QuantumTripleRightOscillator
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

theorem tripleRightDegree_right_shift (n : ℕ) (i : Fin (n+1)) :
    tripleRightDegree n (tripleRightCreationShift n i)=2 := by
  simp [tripleRightDegree,tripleRightCreationShift,Pi.single_apply]

theorem tripleRightDegree_left_shift (n : ℕ) (i : Fin (n+1)) :
    tripleRightDegree n (tripleLeftCreationShift n i)=1 := by
  simp [tripleRightDegree,tripleLeftCreationShift,Pi.single_apply]

theorem tripleRightCreation_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleRightDegree n) a f) :
    CoefficientHomogeneous (tripleRightDegree n) (a+2) (tripleRightCreation q n f) :=
  sumWeightedTranslation_homogeneous (tripleRightDegree n) (tripleRightCreationShift n)
    (tripleRightCreationCoefficient q n) 2 (tripleRightDegree_right_shift n) a f hf

theorem tripleLeftCreation_right_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleRightDegree n) a f) :
    CoefficientHomogeneous (tripleRightDegree n) (a+1) (tripleLeftCreation q n f) :=
  sumWeightedTranslation_homogeneous (tripleRightDegree n) (tripleLeftCreationShift n)
    (tripleLeftCreationCoefficient q n) 1 (tripleRightDegree_left_shift n) a f hf

theorem tripleRightCreation_pow_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleRightDegree n) a f) (t : ℕ) :
    CoefficientHomogeneous (tripleRightDegree n) (a+2*(t:ℤ)) (((tripleRightCreation q n)^t) f) :=
  gradedCreation_pow (tripleRightDegree n) (tripleRightCreation q n) 2 (tripleRightCreation_homogeneous q n) a f hf t

theorem tripleLeftCreation_pow_right_homogeneous (q : ℝ) (n : ℕ) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleRightDegree n) a f) (t : ℕ) :
    CoefficientHomogeneous (tripleRightDegree n) (a+(t:ℤ)) (((tripleLeftCreation q n)^t) f) := by
  simpa only [one_mul] using gradedCreation_pow (tripleRightDegree n) (tripleLeftCreation q n) 1
    (tripleLeftCreation_right_homogeneous q n) a f hf t

theorem tripleCupBase_right_homogeneous (n : ℕ) (l h c : ℤ) :
    CoefficientHomogeneous (tripleRightDegree n) (h+c) (tripleCupBase n l h c) := by
  have h0:=coefficientHomogeneous_single (tripleRightDegree n)
    (Pi.single 0 l,Pi.single (Fin.last n) h,Pi.single 0 c) 1
  simpa only [tripleCupBase,tripleRightDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Pi.single_apply,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h0

theorem tripleRightAnnihilation_creation_homogeneous (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (a : ℤ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : CoefficientHomogeneous (tripleRightDegree n) a f) :
    tripleRightAnnihilation q n (tripleRightCreation q n f)=
      q^(-2:ℤ) • tripleRightCreation q n (tripleRightAnnihilation q n f)+
        (q^(-a-(n:ℤ))*qInteger q (a+(n:ℤ)+1)) • f := by
  have h:=DFunLike.congr_fun (tripleRightAnnihilation_creation_commutator q hq hD n) f
  change tripleRightAnnihilation q n (tripleRightCreation q n f)-
    q^(-2:ℤ) • tripleRightCreation q n (tripleRightAnnihilation q n f)=_ at h
  rw [weightedTranslation_zero_homogeneous (tripleRightDegree n) a f hf
    (fun z : ℤ =>q^(-z-(n:ℤ))*qInteger q (z+(n:ℤ)+1))] at h
  exact (sub_eq_iff_eq_add).mp h |>.trans (add_comm _ _)

theorem tripleRightAnnihilation_creation_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (a : ℤ) (f : OccupationTripleLattice n →₀ ℝ)
    (hf : CoefficientHomogeneous (tripleRightDegree n) a f) (t : ℕ) :
    tripleRightAnnihilation q n (((tripleRightCreation q n)^(t+1)) f)=
      (q^(-2:ℤ))^(t+1) • ((tripleRightCreation q n)^(t+1)) (tripleRightAnnihilation q n f)+
        quantumOscillatorLadderCoefficient q (a+(n:ℤ)) (t+1) • ((tripleRightCreation q n)^t) f := by
  apply gradedOscillator_power (tripleRightCreation q n) (tripleRightAnnihilation q n) (q^(-2:ℤ))
    (quantumOscillatorLadderCoefficient q (a+(n:ℤ)))
    (fun s =>q^(-(a+(n:ℤ))-2*(s:ℤ))*qInteger q (a+(n:ℤ)+2*(s:ℤ)+1))
    (quantumOscillatorLadderCoefficient_zero q (a+(n:ℤ)))
    (quantumOscillatorLadderCoefficient_succ q hq hD (a+(n:ℤ))) f
  intro s
  have h:=tripleRightAnnihilation_creation_homogeneous q hq hD n (a+2*(s:ℤ))
    (((tripleRightCreation q n)^s) f) (tripleRightCreation_pow_homogeneous q n a f hf s)
  have he : -(a+2*(s:ℤ))-(n:ℤ)= -(a+(n:ℤ))-2*(s:ℤ) := by ring
  have he' : a+2*(s:ℤ)+(n:ℤ)+1=a+(n:ℤ)+2*(s:ℤ)+1 := by ring
  rw [he,he'] at h
  simpa only [pow_succ',Module.End.mul_apply] using h

end AMSPhysical

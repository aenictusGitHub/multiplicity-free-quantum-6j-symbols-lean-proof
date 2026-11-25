import EulerDegrees

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

def weightedEuler (w : σ → K) : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) :=
  ∑ i,(w i • (X i : MvPolynomial σ K)) • pderiv i

theorem weightedEuler_apply (w : σ → K) (p : MvPolynomial σ K) :
    weightedEuler w p=∑ i,w i • (X i*pderiv i p) := by
  have he (s : Finset σ) :
      (∑ i∈s,(w i • (X i : MvPolynomial σ K)) • pderiv i) p=
        ∑ i∈s,w i • (X i*pderiv i p) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,Derivation.zero_apply]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi,Derivation.add_apply,ih,Derivation.smul_apply,
        smul_eq_mul,smul_mul_assoc]
  exact he Finset.univ

theorem weightedEuler_X (w : σ → K) (i : σ) : weightedEuler w (X i)=w i • X i := by
  simp [weightedEuler_apply,pderiv_X,Pi.single_apply]

theorem pderiv_weightedEuler (w : σ → K) (i : σ) (p : MvPolynomial σ K) :
    pderiv i (weightedEuler w p)=weightedEuler w (pderiv i p)+w i • pderiv i p := by
  simp only [weightedEuler_apply,map_sum,Derivation.map_smul,pderiv_mul,smul_add,Finset.sum_add_distrib]
  have h₁ : (∑ j : σ,w j • (pderiv i (X j)*pderiv j p))=w i • pderiv i p := by
    simp [pderiv_X,Pi.single_apply]
  rw [h₁]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pd_comm i j]

theorem weightedEuler_pderiv (w : σ → K) (i : σ) (p : MvPolynomial σ K) :
    weightedEuler w (pderiv i p)=pderiv i (weightedEuler w p)-w i • pderiv i p := by
  rw [pderiv_weightedEuler,add_sub_cancel_right]

theorem weightedEuler_balanced_second (w : σ → K) (i j k l : σ)
    (hw : w i+w j=w k+w l) (p : MvPolynomial σ K) :
    weightedEuler w (X i*X j*pderiv k (pderiv l p))=
      X i*X j*pderiv k (pderiv l (weightedEuler w p)) := by
  simp only [Derivation.leibniz,smul_eq_mul,weightedEuler_X,weightedEuler_pderiv,map_sub,Derivation.map_smul,
    mul_sub,mul_smul_comm,smul_mul_assoc,smul_sub]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq]
  have hh : (C (w i):MvPolynomial σ K)+C (w j)=C (w k)+C (w l) := by
    rw [← map_add,← map_add,hw]
  linear_combination (X i*X j*pderiv k (pderiv l p))*hh

end AMSPhysical

#print axioms AMSPhysical.weightedEuler_balanced_second

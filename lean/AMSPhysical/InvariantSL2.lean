import Reduction
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def det2 (a b c d : K) : K := a*d-b*c

/-- The genuine GL(2) action: vectors by g, covectors by g inverse. -/
def twoAction (a b c d : K) (v : Fin 8 → K) : Fin 8 → K := ![
  a*v 0+b*v 1,c*v 0+d*v 1,
  a*v 2+b*v 3,c*v 2+d*v 3,
  (d*v 4-c*v 5)/det2 a b c d,(-b*v 4+a*v 5)/det2 a b c d,
  (d*v 6-c*v 7)/det2 a b c d,(-b*v 6+a*v 7)/det2 a b c d]

def IsRelativeInvariantI (h : ℕ) (p : P8 K) : Prop :=
  ∀ a b c d, det2 a b c d≠0 → ∀ v,
    eval (twoAction a b c d v) p * (det2 a b c d)^h=eval v p

def IsRelativeInvariantII (h : ℕ) (p : P8 K) : Prop :=
  ∀ a b c d, det2 a b c d≠0 → ∀ v,
    eval (twoAction a b c d v) p=(det2 a b c d)^h*eval v p

def covBack : P8 K →ₐ[K] P4 K := aeval ![X 0,X 1,X 2,X 3,1,0,0,1]

def covCanonical (v : Fin 8 → K) : Fin 8 → K := ![
  v 0*v 4+v 1*v 5,v 0*v 6+v 1*v 7,
  v 2*v 4+v 3*v 5,v 2*v 6+v 3*v 7,1,0,0,1]

theorem eval_aeval_substitution {σ τ : Type*} (v : τ → K)
    (s : σ → MvPolynomial τ K) (p : MvPolynomial σ K) :
    eval v (aeval s p)=eval (fun i => eval v (s i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,aeval_X,eval_X,hp]

theorem eval_pull_covBack (p : P8 K) (v : Fin 8 → K) :
    eval v (pull (covBack p))=eval (covCanonical v) p := by
  unfold pull covBack
  rw [eval_aeval_substitution,eval_aeval_substitution]
  apply congrArg (fun w : Fin 8 → K => eval w p)
  funext i
  fin_cases i <;> simp [coords,covCanonical]

theorem twoAction_covectors (v : Fin 8 → K) (hv : v 4*v 7-v 5*v 6≠0) :
    twoAction (v 4) (v 5) (v 6) (v 7) v=covCanonical v := by
  funext i
  have hv2 : v 7*v 4-v 6*v 5≠0 := by simpa [mul_comm] using hv
  fin_cases i <;> simp [twoAction,covCanonical,det2]
  all_goals field_simp [hv,hv2]
  all_goals ring_nf <;> simp

/-- Polynomial equality can be checked off any nonzero polynomial hypersurface. -/
theorem polynomial_eq_off_hypersurface [Infinite K] {σ : Type*}
    (p q D : MvPolynomial σ K) (hD : D≠0)
    (he : ∀ v, eval v D≠0 → eval v p=eval v q) : p=q := by
  have hp : D*(p-q)=0 := by
    apply MvPolynomial.funext
    intro v
    by_cases hv : eval v D=0
    · simp [hv]
    · simp [he v hv]
  have hz := (mul_eq_zero.mp hp).resolve_left hD
  exact sub_eq_zero.mp hz

/-- Surjectivity onto the actual GL(2) relative invariants. This uses the
group action directly and does not assume an invariant-generating theorem. -/
theorem relativeInvariantI_reconstruction [Infinite K] (h : ℕ) (p : P8 K)
    (hp : IsRelativeInvariantI h p) : p=shiftI h (covBack p) := by
  apply polynomial_eq_off_hypersurface p _ detY detY_ne_zero
  intro v hv
  have hv' : v 4*v 7-v 5*v 6≠0 := by simpa [detY] using hv
  have he := hp (v 4) (v 5) (v 6) (v 7) (by simpa [det2] using hv') v
  rw [twoAction_covectors v hv'] at he
  rw [shiftI,map_mul,map_pow,eval_pull_covBack]
  simpa [detY,det2,mul_comm] using he.symm

def vectorCanonical (v : Fin 8 → K) : Fin 8 → K := ![1,0,0,1,
  v 0*v 4+v 1*v 5,v 2*v 4+v 3*v 5,
  v 0*v 6+v 1*v 7,v 2*v 6+v 3*v 7]

theorem eval_pull_evalBack (p : P8 K) (v : Fin 8 → K) :
    eval v (pull (evalBack p))=eval (vectorCanonical v) p := by
  unfold pull evalBack
  rw [eval_aeval_substitution,eval_aeval_substitution]
  apply congrArg (fun w : Fin 8 → K => eval w p)
  funext i
  fin_cases i <;> simp [coords,vectorCanonical]

theorem inverse_vector_det (v : Fin 8 → K) (_hv : v 0*v 3-v 1*v 2≠0) :
    det2 (v 3/(v 0*v 3-v 1*v 2)) (-v 2/(v 0*v 3-v 1*v 2))
      (-v 1/(v 0*v 3-v 1*v 2)) (v 0/(v 0*v 3-v 1*v 2)) =
      (v 0*v 3-v 1*v 2)⁻¹ := by
  unfold det2
  field_simp

theorem twoAction_vectors (v : Fin 8 → K) (hv : v 0*v 3-v 1*v 2≠0) :
    twoAction (v 3/(v 0*v 3-v 1*v 2)) (-v 2/(v 0*v 3-v 1*v 2))
      (-v 1/(v 0*v 3-v 1*v 2)) (v 0/(v 0*v 3-v 1*v 2)) v=vectorCanonical v := by
  have hd := inverse_vector_det v hv
  have hv2 : v 3*v 0-v 1*v 2≠0 := by simpa [mul_comm] using hv
  have hv3 : v 0*v 3-v 2*v 1≠0 := by simpa [mul_comm] using hv
  funext i
  fin_cases i <;> simp [twoAction,vectorCanonical,hd]
  all_goals field_simp [hv,hv2,hv3]
  all_goals ring_nf

theorem relativeInvariantII_reconstruction [Infinite K] (h : ℕ) (p : P8 K)
    (hp : IsRelativeInvariantII h p) : p=shiftII h (evalBack p) := by
  apply polynomial_eq_off_hypersurface p _ detX detX_ne_zero
  intro v hv
  have hv' : v 0*v 3-v 1*v 2≠0 := by simpa [detX] using hv
  have hd := inverse_vector_det v hv'
  have he := hp (v 3/(v 0*v 3-v 1*v 2)) (-v 2/(v 0*v 3-v 1*v 2))
    (-v 1/(v 0*v 3-v 1*v 2)) (v 0/(v 0*v 3-v 1*v 2))
    (by rw [hd]; exact inv_ne_zero hv') v
  rw [twoAction_vectors v hv',hd] at he
  rw [shiftII,map_mul,map_pow,eval_pull_evalBack]
  simp only [detX,map_sub,map_mul,eval_X]
  rw [he]
  simp [← mul_assoc,hv']

end AMSPhysical

#print axioms AMSPhysical.relativeInvariantI_reconstruction

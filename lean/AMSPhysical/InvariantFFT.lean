import InvariantGL

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def covBackN (h : ℕ) : PN K (2+h) →ₐ[K] P4 K := aeval fun ai =>
  Fin.addCases (![![X 0,X 1],![X 2,X 3],![1,0],![0,1]] ai.1)
    (fun _ : Fin h => 0) ai.2

theorem eval_coordsN (n : ℕ) (v : Fin 4×Fin n → K) (i : Fin 4) :
    eval v (coordsN n i)=pairingPoint n v i := by
  fin_cases i <;> simp [coordsN,dotN,pairingPoint,formOf,rowOf,mul_comm]

theorem eval_pull_covBackN (h : ℕ) (p : PN K (2+h)) (v : Fin 4×Fin (2+h) → K) :
    eval v (pullN (2+h) (covBackN h p))=eval (canonicalPoint h v) p := by
  unfold pullN covBackN
  rw [eval_aeval_substitution,eval_aeval_substitution]
  apply congrArg (fun w : Fin 4×Fin (2+h) → K => eval w p)
  funext ⟨a,i⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases a <;> fin_cases j <;>
      simp [canonicalPoint,seedVec,eval_coordsN]
  · fin_cases a <;> simp [canonicalPoint,seedVec]

theorem covBackN_coordsN (h : ℕ) (i : Fin 4) :
    covBackN (K:=K) h (coordsN (2+h) i)=X i := by
  fin_cases i <;> simp [coordsN,dotN,covBackN,Fin.sum_univ_add,Fin.sum_univ_succ]

theorem covBackN_pullN (h : ℕ) (f : P4 K) : covBackN h (pullN (2+h) f)=f := by
  have he : (covBackN h : PN K (2+h) →ₐ[K] P4 K).comp (pullN (2+h))=
      AlgHom.id K (P4 K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [pullN,covBackN_coordsN]
  exact DFunLike.congr_fun he f

theorem pullN_injective (h : ℕ) : Function.Injective (pullN (R:=K) (2+h)) :=
  Function.LeftInverse.injective (covBackN_pullN h)

def pairingDet (n : ℕ) : PN K n :=
  coordsN n 0*coordsN n 3-coordsN n 1*coordsN n 2

theorem pairingDet_ne_zero (h : ℕ) : (pairingDet (2+h) : PN K (2+h))≠0 := by
  intro hz
  have he := congrArg (fun p : PN K (2+h) => covBackN h p) hz
  simp only [pairingDet,map_sub,map_mul,covBackN_coordsN,map_zero] at he
  have hf := congrArg (fun p : P4 K => eval ![1,0,0,1] p) he
  simp at hf

/-- The full vector/covector first fundamental theorem for two vectors and
two covectors, for every rank at least two. The proof uses generic GL orbits
and polynomial extensionality, not an assumed invariant-generation result. -/
theorem gl_invariant_reconstruction [Infinite K] (h : ℕ) (p : PN K (2+h))
    (hp : IsGLInvariant (2+h) p) : p=pullN (2+h) (covBackN h p) := by
  apply polynomial_eq_off_hypersurface p _ (pairingDet (2+h)) (pairingDet_ne_zero h)
  intro v hv
  have hv' : det2 (pairingPoint (2+h) v 0) (pairingPoint (2+h) v 2)
      (pairingPoint (2+h) v 1) (pairingPoint (2+h) v 3)≠0 := by
    simpa [pairingDet,det2,eval_coordsN,mul_comm] using hv
  obtain ⟨g,hg⟩ := nondegenerate_point_orbit h v hv'
  have he := hp g v
  rw [hg] at he
  rw [eval_pull_covBackN]
  exact he.symm

theorem pairingPoint_action (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (v : Fin 4×Fin n → K) (i : Fin 4) :
    pairingPoint n (pointAction n g v) i=pairingPoint n v i := by
  have hx : rowOf n (pointAction n g v) 0=g (rowOf n v 0) := rfl
  have hz : rowOf n (pointAction n g v) 1=g (rowOf n v 1) := rfl
  fin_cases i
  · change formOf n (pointAction n g v) 2 (rowOf n (pointAction n g v) 0)=_
    rw [action_covector n g v 2 (Or.inl rfl),hx,LinearEquiv.symm_apply_apply]
    rfl
  · change formOf n (pointAction n g v) 3 (rowOf n (pointAction n g v) 0)=_
    rw [action_covector n g v 3 (Or.inr rfl),hx,LinearEquiv.symm_apply_apply]
    rfl
  · change formOf n (pointAction n g v) 2 (rowOf n (pointAction n g v) 1)=_
    rw [action_covector n g v 2 (Or.inl rfl),hz,LinearEquiv.symm_apply_apply]
    rfl
  · change formOf n (pointAction n g v) 3 (rowOf n (pointAction n g v) 1)=_
    rw [action_covector n g v 3 (Or.inr rfl),hz,LinearEquiv.symm_apply_apply]
    rfl

theorem pullN_gl_invariant (n : ℕ) (f : P4 K) : IsGLInvariant n (pullN n f) := by
  intro g v
  unfold pullN
  rw [eval_aeval_substitution,eval_aeval_substitution]
  apply congrArg (fun w : Fin 4 → K => eval w f)
  funext i
  rw [eval_coordsN,eval_coordsN,pairingPoint_action]

def glInvariantAlgebra (n : ℕ) : Subalgebra K (PN K n) where
  carrier := {p | IsGLInvariant n p}
  zero_mem' := by intro g v; simp
  one_mem' := by intro g v; simp
  add_mem' := by intro p q hp hq g v; simp only [map_add,hp g v,hq g v]
  mul_mem' := by intro p q hp hq g v; simp only [map_mul,hp g v,hq g v]
  algebraMap_mem' := by intro c g v; simp [MvPolynomial.algebraMap_eq]

/-- The complete invariant-algebra identification at every rank N>=2. -/
def glInvariantEquiv [Infinite K] (h : ℕ) :
    P4 K ≃ₐ[K] glInvariantAlgebra (K:=K) (2+h) where
  toFun f := ⟨pullN (2+h) f,pullN_gl_invariant (2+h) f⟩
  invFun p := covBackN h p.val
  left_inv := covBackN_pullN h
  right_inv p := by
    apply Subtype.ext
    exact (gl_invariant_reconstruction h p.val p.property).symm
  map_mul' f g := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; simp
  commutes' c := by apply Subtype.ext; simp [MvPolynomial.algebraMap_eq]

end AMSPhysical

#print axioms AMSPhysical.gl_invariant_reconstruction

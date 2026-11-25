import InvariantSL2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

theorem twoAction_pairings (a b c d : K) (hD : det2 a b c d≠0)
    (v : Fin 8 → K) (i : Fin 4) :
    eval (twoAction a b c d v) (coords i)=eval v (coords i) := by
  fin_cases i <;> simp [coords,twoAction]
  all_goals field_simp [hD]
  all_goals unfold det2
  all_goals ring

theorem twoAction_pull (a b c d : K) (hD : det2 a b c d≠0)
    (v : Fin 8 → K) (f : P4 K) :
    eval (twoAction a b c d v) (pull f)=eval v (pull f) := by
  unfold pull
  rw [eval_aeval_substitution,eval_aeval_substitution]
  apply congrArg (fun w : Fin 4 → K => eval w f)
  funext i
  exact twoAction_pairings a b c d hD v i

theorem twoAction_detY (a b c d : K) (hD : det2 a b c d≠0)
    (v : Fin 8 → K) :
    eval (twoAction a b c d v) detY*det2 a b c d=eval v detY := by
  simp [detY,twoAction]
  field_simp [hD]
  unfold det2
  ring

theorem twoAction_detX (a b c d : K) (v : Fin 8 → K) :
    eval (twoAction a b c d v) detX=det2 a b c d*eval v detX := by
  simp [detX,twoAction,det2]
  ring

theorem shiftI_relative (h : ℕ) (f : P4 K) : IsRelativeInvariantI h (shiftI h f) := by
  intro a b c d hD v
  simp only [shiftI,map_mul,map_pow]
  calc
    eval (twoAction a b c d v) detY^h*eval (twoAction a b c d v) (pull f)*
        det2 a b c d^h =
      (eval (twoAction a b c d v) detY*det2 a b c d)^h*
        eval (twoAction a b c d v) (pull f) := by rw [mul_pow]; ring
    _=eval v detY^h*eval v (pull f) := by
      rw [twoAction_detY a b c d hD,twoAction_pull a b c d hD]

theorem shiftII_relative (h : ℕ) (f : P4 K) : IsRelativeInvariantII h (shiftII h f) := by
  intro a b c d hD v
  simp only [shiftII,map_mul,map_pow,twoAction_detX,twoAction_pull a b c d hD,mul_pow]
  ring

theorem covBack_pull (f : P4 K) : covBack (pull f)=f := by
  have he : (covBack : P8 K →ₐ[K] P4 K).comp pull=AlgHom.id K (P4 K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [covBack,pull,coords]
  exact DFunLike.congr_fun he f

theorem covBack_shiftI (h : ℕ) (f : P4 K) : covBack (shiftI h f)=f := by
  simp only [shiftI,map_mul,map_pow,covBack_pull]
  have hd : covBack (detY : P8 K)=1 := by simp [covBack,detY]
  rw [hd,one_pow,one_mul]

theorem evalBack_shiftII (h : ℕ) (f : P4 K) : evalBack (shiftII h f)=f := by
  simp only [shiftII,map_mul,map_pow,evalBack_pull]
  have hd : evalBack (detX : P8 K)=1 := by simp [evalBack,detX]
  rw [hd,one_pow,one_mul]

def relativeSpaceI (h : ℕ) : Submodule K (P8 K) where
  carrier := {p | IsRelativeInvariantI h p}
  zero_mem' := by intro a b c d hD v; simp
  add_mem' := by
    intro p q hp hq a b c d hD v
    simp only [map_add,add_mul,hp a b c d hD v,hq a b c d hD v]
  smul_mem' := by
    intro c p hp a b c' d hD v
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C]
    rw [mul_assoc,hp a b c' d hD v]

def relativeSpaceII (h : ℕ) : Submodule K (P8 K) where
  carrier := {p | IsRelativeInvariantII h p}
  zero_mem' := by intro a b c d hD v; simp
  add_mem' := by
    intro p q hp hq a b c d hD v
    simp only [map_add,mul_add,hp a b c d hD v,hq a b c d hD v]
  smul_mem' := by
    intro c p hp a b c' d hD v
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C]
    rw [hp a b c' d hD v]
    ring

/-- Explicit linear equivalence with the full GL(2) relative-invariant space. -/
def typeI_relativeEquiv [Infinite K] (h : ℕ) : P4 K ≃ₗ[K] relativeSpaceI (K:=K) h where
  toFun f := ⟨shiftI h f,shiftI_relative h f⟩
  invFun p := covBack p.val
  left_inv := covBack_shiftI h
  right_inv p := by
    apply Subtype.ext
    exact (relativeInvariantI_reconstruction h p.val p.property).symm
  map_add' f g := by
    apply Subtype.ext
    simp [shiftI,mul_add]
  map_smul' c f := by
    apply Subtype.ext
    simp [shiftI,mul_smul_comm]

def typeII_relativeEquiv [Infinite K] (h : ℕ) : P4 K ≃ₗ[K] relativeSpaceII (K:=K) h where
  toFun f := ⟨shiftII h f,shiftII_relative h f⟩
  invFun p := evalBack p.val
  left_inv := evalBack_shiftII h
  right_inv p := by
    apply Subtype.ext
    exact (relativeInvariantII_reconstruction h p.val p.property).symm
  map_add' f g := by
    apply Subtype.ext
    simp [shiftII,mul_add]
  map_smul' c f := by
    apply Subtype.ext
    simp [shiftII,mul_smul_comm]

end AMSPhysical

#print axioms AMSPhysical.typeI_relativeEquiv
#print axioms AMSPhysical.typeII_relativeEquiv

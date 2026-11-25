import SplitOrbit
import InvariantSL2
import Radial
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

abbrev Vec (K : Type*) (n : ℕ) := Fin n → K

def rowOf (n : ℕ) (v : Fin 4×Fin n → K) (a : Fin 4) : Vec K n := fun i => v (a,i)

def formOf (n : ℕ) (v : Fin 4×Fin n → K) (a : Fin 4) : Vec K n →ₗ[K] K where
  toFun u := ∑ i,v (a,i)*u i
  map_add' u w := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]

theorem linear_form_expansion (n : ℕ) (L : Vec K n →ₗ[K] K) (u : Vec K n) :
    L u=∑ i,L (Pi.single i 1)*u i := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Pi.single i (u i)=u i • (Pi.single i 1 : Vec K n) := by
    funext j
    by_cases hj : j=i <;> simp [Pi.single_apply,hj]
  rw [he,map_smul,smul_eq_mul]
  ring

/-- The ordinary GL(n) action on two vectors and two covectors. -/
def pointAction (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (v : Fin 4×Fin n → K) : Fin 4×Fin n → K := fun ai =>
  ![g (rowOf n v 0),g (rowOf n v 1),
    (fun i => formOf n v 2 (g.symm (Pi.single i 1))),
    (fun i => formOf n v 3 (g.symm (Pi.single i 1)))] ai.1 ai.2

def IsGLInvariant (n : ℕ) (p : PN K n) : Prop :=
  ∀ g : Vec K n ≃ₗ[K] Vec K n, ∀ v, eval (pointAction n g v) p=eval v p

theorem formOf_single (n : ℕ) (v : Fin 4×Fin n → K) (a : Fin 4) (i : Fin n) :
    formOf n v a (Pi.single i 1)=v (a,i) := by
  simp [formOf,Pi.single_apply,mul_ite]

theorem action_covector (n : ℕ) (g : Vec K n ≃ₗ[K] Vec K n)
    (v : Fin 4×Fin n → K) (a : Fin 4) (ha : a=2 ∨ a=3) (u : Vec K n) :
    formOf n (pointAction n g v) a u=formOf n v a (g.symm u) := by
  have he := linear_form_expansion n ((formOf n v a).comp g.symm.toLinearMap) u
  rcases ha with rfl | rfl
  · simpa [formOf,pointAction] using he.symm
  · simpa [formOf,pointAction] using he.symm

def twoLin (a b c d : K) : Vec K 2 →ₗ[K] Vec K 2 where
  toFun u := ![a*u 0+b*u 1,c*u 0+d*u 1]
  map_add' u w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' t u := by ext i; fin_cases i <;> simp <;> ring

def twoEquiv (a b c d : K) (hd : det2 a b c d≠0) : Vec K 2 ≃ₗ[K] Vec K 2 where
  toFun := twoLin a b c d
  invFun := twoLin (d/det2 a b c d) (-b/det2 a b c d)
    (-c/det2 a b c d) (a/det2 a b c d)
  left_inv u := by
    ext i
    fin_cases i <;> simp [twoLin]
    all_goals field_simp [hd]
    all_goals unfold det2
    all_goals ring
  right_inv u := by
    ext i
    fin_cases i <;> simp [twoLin]
    all_goals field_simp [hd]
    all_goals unfold det2
    all_goals ring
  map_add' := (twoLin a b c d).map_add
  map_smul' := (twoLin a b c d).map_smul

def seedVec (h : ℕ) : Vec K 2 →ₗ[K] Vec K (2+h) where
  toFun u := Fin.addCases u (fun _ : Fin h => 0)
  map_add' u w := by ext i; refine Fin.addCases ?_ ?_ i <;> simp
  map_smul' t u := by ext i; refine Fin.addCases ?_ ?_ i <;> simp

def projectVec (h : ℕ) : Vec K (2+h) →ₗ[K] Vec K 2 where
  toFun v := fun i => v (Fin.castAdd h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem project_seed (h : ℕ) (u : Vec K 2) : projectVec h (seedVec h u)=u := by
  ext i
  simp [projectVec,seedVec]

theorem seed_single (h : ℕ) (i : Fin 2) :
    seedVec h (Pi.single i 1 : Vec K 2)=Pi.single (Fin.castAdd h i) 1 := by
  ext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [seedVec,Pi.single_apply]
  · simp [seedVec,Pi.single_apply,Fin.ext_iff]
    omega

def frameVectors (n : ℕ) (v : Fin 4×Fin n → K) : Vec K 2 →ₗ[K] Vec K n where
  toFun u := u 0 • rowOf n v 0+u 1 • rowOf n v 1
  map_add' u w := by simp [add_smul]; module
  map_smul' t u := by simp [smul_add,mul_smul]

def frameCovectors (n : ℕ) (v : Fin 4×Fin n → K) : Vec K n →ₗ[K] Vec K 2 where
  toFun u := ![formOf n v 2 u,formOf n v 3 u]
  map_add' u w := by ext i; fin_cases i <;> simp
  map_smul' t u := by ext i; fin_cases i <;> simp

def pairingPoint (n : ℕ) (v : Fin 4×Fin n → K) : Fin 4 → K := ![
  formOf n v 2 (rowOf n v 0),formOf n v 3 (rowOf n v 0),
  formOf n v 2 (rowOf n v 1),formOf n v 3 (rowOf n v 1)]

def canonicalPoint (h : ℕ) (v : Fin 4×Fin (2+h) → K) : Fin 4×Fin (2+h) → K :=
  fun ai => ![seedVec h ![pairingPoint (2+h) v 0,pairingPoint (2+h) v 1],
    seedVec h ![pairingPoint (2+h) v 2,pairingPoint (2+h) v 3],
    seedVec h ![1,0],seedVec h ![0,1]] ai.1 ai.2

theorem frame_vectors_single (n : ℕ) (v : Fin 4×Fin n → K) (i : Fin 2) :
    frameVectors n v (Pi.single i 1)=![rowOf n v 0,rowOf n v 1] i := by
  fin_cases i <;> simp [frameVectors,Pi.single_apply]

theorem frame_composition (n : ℕ) (v : Fin 4×Fin n → K) (u : Vec K 2) :
    frameCovectors n v (frameVectors n v u)=
      twoLin (pairingPoint n v 0) (pairingPoint n v 2)
        (pairingPoint n v 1) (pairingPoint n v 3) u := by
  ext i
  fin_cases i <;> simp [frameCovectors,frameVectors,twoLin,pairingPoint,mul_comm]

theorem nondegenerate_point_orbit (h : ℕ) (v : Fin 4×Fin (2+h) → K)
    (hv : det2 (pairingPoint (2+h) v 0) (pairingPoint (2+h) v 2)
      (pairingPoint (2+h) v 1) (pairingPoint (2+h) v 3)≠0) :
    ∃ g : Vec K (2+h) ≃ₗ[K] Vec K (2+h), pointAction (2+h) g v=canonicalPoint h v := by
  let Z := twoEquiv (pairingPoint (2+h) v 0) (pairingPoint (2+h) v 2)
    (pairingPoint (2+h) v 1) (pairingPoint (2+h) v 3) hv
  obtain ⟨g,hg,hY⟩ := nondegenerate_frame_orbit (frameVectors (2+h) v)
    (seedVec h) (frameCovectors (2+h) v) (projectVec h) Z
    (frame_composition (2+h) v) (project_seed h)
  refine ⟨g,?_⟩
  have hx := hg (Pi.single (0:Fin 2) 1)
  have hz := hg (Pi.single (1:Fin 2) 1)
  rw [frame_vectors_single] at hx hz
  have hy (i : Fin (2+h)) :
      formOf (2+h) v 2 (g.symm (Pi.single i 1))=
        (seedVec h ![1,0] : Vec K (2+h)) i := by
    have he := congrFun (hY (g.symm (Pi.single i 1))) (0:Fin 2)
    simp only [LinearEquiv.apply_symm_apply,projectVec,LinearMap.coe_mk,AddHom.coe_mk,
      frameCovectors,Matrix.cons_val_zero] at he
    rw [← he]
    have hs := seed_single (K:=K) h (0:Fin 2)
    have hb : (Pi.single (0:Fin 2) 1 : Vec K 2)=![1,0] := by
      ext j; fin_cases j <;> simp [Pi.single_apply]
    rw [hb] at hs
    simpa [Pi.single_apply,eq_comm] using congrFun hs i |>.symm
  have hw (i : Fin (2+h)) :
      formOf (2+h) v 3 (g.symm (Pi.single i 1))=
        (seedVec h ![0,1] : Vec K (2+h)) i := by
    have he := congrFun (hY (g.symm (Pi.single i 1))) (1:Fin 2)
    simp only [LinearEquiv.apply_symm_apply,projectVec,LinearMap.coe_mk,AddHom.coe_mk,
      frameCovectors,Matrix.cons_val_one,Matrix.cons_val_zero] at he
    rw [← he]
    have hs := seed_single (K:=K) h (1:Fin 2)
    have hb : (Pi.single (1:Fin 2) 1 : Vec K 2)=![0,1] := by
      ext j; fin_cases j <;> simp [Pi.single_apply]
    rw [hb] at hs
    simpa [Pi.single_apply,eq_comm] using congrFun hs i |>.symm
  funext ⟨a,i⟩
  fin_cases a
  · simpa [pointAction,canonicalPoint,Z,twoEquiv,twoLin,Pi.single_apply] using congrFun hx i
  · simpa [pointAction,canonicalPoint,Z,twoEquiv,twoLin,Pi.single_apply] using congrFun hz i
  · exact hy i
  · exact hw i

end AMSPhysical

#print axioms AMSPhysical.action_covector
#print axioms AMSPhysical.twoEquiv

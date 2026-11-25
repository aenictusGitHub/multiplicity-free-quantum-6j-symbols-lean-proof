import EulerDegrees
import RelativeEquiv
import SL2Charge
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def unpackEight : P8 K ≃ₐ[K] PN K 2 :=
  renameEquiv K (finProdFinEquiv : Fin 4×Fin 2 ≃ Fin 8).symm

theorem unpackEight_pderiv (i : Fin 8) (p : P8 K) :
    unpackEight (pderiv i p)=
      pderiv ((finProdFinEquiv : Fin 4×Fin 2 ≃ Fin 8).symm i) (unpackEight p) := by
  exact (pderiv_rename (Equiv.injective _) i p).symm

def eulerEight (a : Fin 4) : Derivation K (P8 K) (P8 K) := ![
  (X 0 : P8 K) • (pderiv 0 : Derivation K (P8 K) (P8 K))+(X 1 : P8 K) • pderiv 1,
  (X 2 : P8 K) • pderiv 2+(X 3 : P8 K) • pderiv 3,
  (X 4 : P8 K) • pderiv 4+(X 5 : P8 K) • pderiv 5,
  (X 6 : P8 K) • pderiv 6+(X 7 : P8 K) • pderiv 7] a

theorem unpackEight_euler (a : Fin 4) (p : P8 K) :
    unpackEight (eulerEight a p)=eulerFamily 2 a (unpackEight p) := by
  fin_cases a <;> simp [eulerEight,smul_eq_mul,unpackEight_pderiv]
  all_goals simp [eulerFamily,Fin.sum_univ_succ,unpackEight,renameEquiv_apply,finProdFinEquiv]
  all_goals rfl

theorem unpackEight_pull (f : P4 K) : unpackEight (pull f)=pullN 2 f := by
  have he : (unpackEight : P8 K ≃ₐ[K] PN K 2).toAlgHom.comp pull=pullN 2 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [unpackEight,pull,pullN,coords,coordsN,dotN,Fin.sum_univ_succ,finProdFinEquiv]
    all_goals rfl
  exact DFunLike.congr_fun he f

theorem eulerEight_pull (a : Fin 4) (f : P4 K) :
    eulerEight a (pull f)=pull (eulerContraction a f) := by
  apply (unpackEight : P8 K ≃ₐ[K] PN K 2).injective
  rw [unpackEight_euler,unpackEight_pull,eulerFamily_pullN,unpackEight_pull]

def familySpaceEight (r : Fin 4 → ℕ) : Submodule K (P8 K) :=
  (familySpace 2 r).comap (unpackEight : P8 K ≃ₐ[K] PN K 2).toLinearMap

theorem familySpaceEight_iff_euler [CharZero K] (r : Fin 4 → ℕ) (p : P8 K) :
    p∈familySpaceEight r ↔ ∀ a,eulerEight a p=(r a:K) • p := by
  change unpackEight p∈familySpace 2 r ↔ _
  rw [familySpace_iff_euler]
  constructor
  · intro hp a
    apply (unpackEight : P8 K ≃ₐ[K] PN K 2).injective
    simpa only [unpackEight_euler,map_smul] using hp a
  · intro hp a
    rw [← unpackEight_euler,hp a,map_smul]

def degreeShiftI (h : ℕ) : Fin 4 → ℕ := ![0,0,h,h]
def degreeShiftII (h : ℕ) : Fin 4 → ℕ := ![h,h,0,0]

theorem eulerEight_detY (a : Fin 4) :
    eulerEight (K:=K) a detY=(degreeShiftI 1 a:K) • detY := by
  fin_cases a <;> simp [eulerEight,detY,degreeShiftI,pderiv_mul,smul_eq_mul] <;> ring

theorem eulerEight_detX (a : Fin 4) :
    eulerEight (K:=K) a detX=(degreeShiftII 1 a:K) • detX := by
  fin_cases a <;> simp [eulerEight,detX,degreeShiftII,pderiv_mul,smul_eq_mul] <;> ring

theorem eulerEight_detY_pow (a : Fin 4) (h : ℕ) :
    eulerEight (K:=K) a (detY^h)=(degreeShiftI h a:K) • detY^h := by
  induction h with
  | zero => fin_cases a <;> simp [degreeShiftI]
  | succ h ih =>
    rw [pow_succ,Derivation.leibniz,ih,eulerEight_detY]
    fin_cases a <;> simp [degreeShiftI,smul_eq_mul,Algebra.smul_def,MvPolynomial.algebraMap_eq]
    all_goals ring

theorem eulerEight_detX_pow (a : Fin 4) (h : ℕ) :
    eulerEight (K:=K) a (detX^h)=(degreeShiftII h a:K) • detX^h := by
  induction h with
  | zero => fin_cases a <;> simp [degreeShiftII]
  | succ h ih =>
    rw [pow_succ,Derivation.leibniz,ih,eulerEight_detX]
    fin_cases a <;> simp [degreeShiftII,smul_eq_mul,Algebra.smul_def,MvPolynomial.algebraMap_eq]
    all_goals ring

theorem eulerEight_shiftI (a : Fin 4) (h : ℕ) (f : P4 K) :
    eulerEight a (shiftI h f)=shiftI h (eulerContraction a f)+
      (degreeShiftI h a:K) • shiftI h f := by
  unfold shiftI
  rw [Derivation.leibniz,eulerEight_pull,eulerEight_detY_pow]
  simp [smul_eq_mul,mul_smul_comm,mul_comm]

theorem eulerEight_shiftII (a : Fin 4) (h : ℕ) (f : P4 K) :
    eulerEight a (shiftII h f)=shiftII h (eulerContraction a f)+
      (degreeShiftII h a:K) • shiftII h f := by
  unfold shiftII
  rw [Derivation.leibniz,eulerEight_pull,eulerEight_detX_pow]
  simp [smul_eq_mul,mul_smul_comm,mul_comm]

end AMSPhysical

#print axioms AMSPhysical.eulerEight_shiftI
#print axioms AMSPhysical.eulerEight_shiftII

import FixedCasimirEnds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

def contractionWeight (a i : Fin 4) : K := ![![1,1,0,0],![0,0,1,1],![1,0,1,0],![0,1,0,1]] a i

theorem eulerContraction_weighted (a : Fin 4) (p : P4 K) :
    eulerContraction a p=weightedEuler (contractionWeight a) p := by
  fin_cases a <;> simp [eulerContraction,weightedEuler_apply,contractionWeight,Fin.sum_univ_succ]

theorem sourceOmegaXX_expansion (p : P4 K) : sourceOmegaXX p=
    X 0*X 2*pderiv 2 (pderiv 0 p)+X 0*X 3*pderiv 2 (pderiv 1 p)+
    X 1*X 2*pderiv 3 (pderiv 0 p)+X 1*X 3*pderiv 3 (pderiv 1 p) := by
  simp [sourceOmegaXX,sourceRaise,sourceLower,sourceEulerX,pderiv_mul]
  ring

theorem weightedEuler_sourceOmegaXX (w : Fin 4 → K) (hw : w 0+w 3=w 1+w 2) (p : P4 K) :
    weightedEuler w (sourceOmegaXX p)=sourceOmegaXX (weightedEuler w p) := by
  simp only [sourceOmegaXX_expansion,map_add]
  rw [weightedEuler_balanced_second w 0 2 2 0 (add_comm _ _) p,
    weightedEuler_balanced_second w 0 3 2 1 (by rw [hw,add_comm]) p,
    weightedEuler_balanced_second w 1 2 3 0 (by rw [← hw,add_comm]) p,
    weightedEuler_balanced_second w 1 3 3 1 (add_comm _ _) p]

theorem sourceOmegaXX_preserves (r : Fin 4 → ℕ) (p : P4 K) (hp : p∈fixedContractions r) :
    sourceOmegaXX p∈fixedContractions r := by
  apply (fixedContractions_iff r _).mpr
  intro a
  have hw : contractionWeight (K:=K) a 0+contractionWeight a 3=
      contractionWeight a 1+contractionWeight a 2 := by
    fin_cases a
    · change (1:K)+0=1+0; rfl
    · change (0:K)+1=0+1; rfl
    · change (1:K)+0=0+1; simp
    · change (0:K)+1=1+0; simp
  rw [eulerContraction_weighted,weightedEuler_sourceOmegaXX _ hw,← eulerContraction_weighted,
    (fixedContractions_iff r p).mp hp a]
  simp only [sourceOmegaXX_expansion,Derivation.map_smul,mul_smul_comm,← smul_add]

def sourceXXEnd (r : Fin 4 → ℕ) : Module.End K (fixedContractions (K:=K) r) where
  toFun p := ⟨sourceOmegaXX p.val,sourceOmegaXX_preserves r p.val p.property⟩
  map_add' p q := by
    apply Subtype.ext
    simp [sourceOmegaXX_expansion,mul_add]
    ring
  map_smul' c p := by
    apply Subtype.ext
    change sourceOmegaXX (c • p.val)=c • sourceOmegaXX p.val
    simp only [sourceOmegaXX_expansion,Derivation.map_smul,mul_smul_comm,← smul_add]

theorem colorRaise_pullN (n : ℕ) (f : P4 K) :
    colorN n 0 1 (pullN n f)=pullN n (sourceRaise f) := by
  simp [colorN,dz_pullN,sourceRaise,pullN_X,coordsN,dotN,Finset.sum_add_distrib,
    Finset.sum_mul,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm]

theorem colorLower_pullN (n : ℕ) (f : P4 K) :
    colorN n 1 0 (pullN n f)=pullN n (sourceLower f) := by
  simp [colorN,dx_pullN,sourceLower,pullN_X,coordsN,dotN,Finset.sum_add_distrib,
    Finset.sum_mul,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm]

theorem colorEuler_pullN (n : ℕ) (f : P4 K) :
    colorN n 0 0 (pullN n f)=pullN n (sourceEulerX f) := by
  simp [colorN,dx_pullN,sourceEulerX,pullN_X,coordsN,dotN,Finset.sum_add_distrib,
    Finset.sum_mul,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm]

theorem sameSource_pullN (n : ℕ) (f : P4 K) :
    colorN n 0 1 (colorN n 1 0 (pullN n f))-colorN n 0 0 (pullN n f)=
      pullN n (sourceOmegaXX f) := by
  rw [colorLower_pullN,colorRaise_pullN,colorEuler_pullN]
  simp only [sourceOmegaXX,map_sub]

variable [Infinite K]

def glXXEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedGLInvariants (K:=K) (2+h) r) :=
  (fixedGLContractionEquiv h r).conj (sourceXXEnd r)

def typeIIXXEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedRelativeII (K:=K) h r) :=
  (fixedTypeIIEquiv h r).conj (sourceXXEnd r)

theorem glXXEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    (glXXEnd h r p).val=colorN (2+h) 0 1 (colorN (2+h) 1 0 p.val)-colorN (2+h) 0 0 p.val := by
  change pullN (2+h) (sourceOmegaXX (covBackN h p.val))=_
  rw [← sameSource_pullN,← gl_invariant_reconstruction h p.val p.property.2]

theorem typeIIXXEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedRelativeII (K:=K) h r) :
    (typeIIXXEnd h r p).val=omegaXX p.val+(h:P8 K)*p.val := by
  change shiftII h (sourceOmegaXX (evalBack p.val))=_
  have he := typeII_same_casimir h (evalBack p.val)
  rw [← relativeInvariantII_reconstruction h p.val p.property.2] at he
  linear_combination -he

theorem rankReductionII_XX (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    classicalRankReductionII h r (glXXEnd h r p)=typeIIXXEnd h r (classicalRankReductionII h r p) := by
  simp [classicalRankReductionII,glXXEnd,typeIIXXEnd,LinearEquiv.conj_apply_apply]

end AMSPhysical

#print axioms AMSPhysical.rankReductionII_XX

import FixedCasimir

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

def sourceXYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedContractions (K:=K) r) where
  toFun f := ⟨mixedXYSource (h+2) f.val,mixedXYSource_preserves h r f.val f.property⟩
  map_add' f g := by
    apply Subtype.ext
    simp [mixedXYSource,radialXY,mul_add]
    ring
  map_smul' c f := by
    apply Subtype.ext
    change mixedXYSource (h+2) (c • f.val)=c • mixedXYSource (h+2) f.val
    simp only [mixedXYSource,radialXY,Derivation.map_smul,mul_smul_comm,← smul_add]

def sourceZYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedContractions (K:=K) r) where
  toFun f := ⟨mixedZYSource (h+2) f.val,mixedZYSource_preserves h r f.val f.property⟩
  map_add' f g := by
    apply Subtype.ext
    simp [mixedZYSource,radialZY,mul_add]
    ring
  map_smul' c f := by
    apply Subtype.ext
    change mixedZYSource (h+2) (c • f.val)=c • mixedZYSource (h+2) f.val
    simp only [mixedZYSource,radialZY,Derivation.map_smul,mul_smul_comm,← smul_add]

variable [Infinite K]

def glXYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedGLInvariants (K:=K) (2+h) r) :=
  (fixedGLContractionEquiv h r).conj (sourceXYEnd h r)

def glZYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedGLInvariants (K:=K) (2+h) r) :=
  (fixedGLContractionEquiv h r).conj (sourceZYEnd h r)

def typeIXYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedRelativeI (K:=K) h r) :=
  (fixedTypeIEquiv h r).conj (sourceXYEnd h r)

def typeIZYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedRelativeI (K:=K) h r) :=
  (fixedTypeIEquiv h r).conj (sourceZYEnd h r)

def typeIIZYEnd (h : ℕ) (r : Fin 4 → ℕ) : Module.End K (fixedRelativeII (K:=K) h r) :=
  (fixedTypeIIEquiv h r).conj (sourceZYEnd h r)

/-- The restricted operators have the actual polynomial Casimir action. -/
theorem glXYEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    (glXYEnd h r p).val=dotN (2+h) 0 2*lapN (2+h) 0 2 p.val := by
  change pullN (2+h) (mixedXYSource (h+2) (covBackN h p.val))=_
  rw [Nat.add_comm h 2,← mixedXYSource_pullN,← gl_invariant_reconstruction h p.val p.property.2]

theorem glZYEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    (glZYEnd h r p).val=dotN (2+h) 1 2*lapN (2+h) 1 2 p.val := by
  change pullN (2+h) (mixedZYSource (h+2) (covBackN h p.val))=_
  rw [Nat.add_comm h 2,← mixedZYSource_pullN,← gl_invariant_reconstruction h p.val p.property.2]

theorem typeIXYEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedRelativeI (K:=K) h r) :
    (typeIXYEnd h r p).val=mixedXYAmbient p.val := by
  change shiftI h (mixedXYSource (h+2) (covBack p.val))=_
  rw [← typeI_pair12,← relativeInvariantI_reconstruction h p.val p.property.2]

theorem typeIZYEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedRelativeI (K:=K) h r) :
    (typeIZYEnd h r p).val=mixedZYAmbient p.val := by
  change shiftI h (mixedZYSource (h+2) (covBack p.val))=_
  rw [← typeI_pair23,← relativeInvariantI_reconstruction h p.val p.property.2]

theorem typeIIZYEnd_val (h : ℕ) (r : Fin 4 → ℕ) (p : fixedRelativeII (K:=K) h r) :
    (typeIIZYEnd h r p).val=mixedZYAmbient p.val := by
  change shiftII h (mixedZYSource (h+2) (evalBack p.val))=_
  rw [← typeII_pair23,← relativeInvariantII_reconstruction h p.val p.property.2]

theorem rankReductionI_XY (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    classicalRankReductionI h r (glXYEnd h r p)=typeIXYEnd h r (classicalRankReductionI h r p) := by
  simp [classicalRankReductionI,glXYEnd,typeIXYEnd,LinearEquiv.conj_apply_apply]

theorem rankReductionI_ZY (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    classicalRankReductionI h r (glZYEnd h r p)=typeIZYEnd h r (classicalRankReductionI h r p) := by
  simp [classicalRankReductionI,glZYEnd,typeIZYEnd,LinearEquiv.conj_apply_apply]

theorem rankReductionII_ZY (h : ℕ) (r : Fin 4 → ℕ) (p : fixedGLInvariants (K:=K) (2+h) r) :
    classicalRankReductionII h r (glZYEnd h r p)=typeIIZYEnd h r (classicalRankReductionII h r p) := by
  simp [classicalRankReductionII,glZYEnd,typeIIZYEnd,LinearEquiv.conj_apply_apply]

end AMSPhysical

#print axioms AMSPhysical.rankReductionI_XY
#print axioms AMSPhysical.rankReductionI_ZY
#print axioms AMSPhysical.rankReductionII_ZY

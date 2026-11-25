import DeterminantDegrees

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def fixedContractions (r : Fin 4 → ℕ) : Submodule K (P4 K) :=
  (familySpace 2 r).comap (pullN (R:=K) 2).toLinearMap

theorem fixedContractions_iff [CharZero K] (r : Fin 4 → ℕ) (f : P4 K) :
    f∈fixedContractions r ↔ ∀ a,eulerContraction a f=(r a:K) • f :=
  contraction_degree_reflection 0 r f

theorem fixedContractions_rank [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) (f : P4 K) :
    f∈fixedContractions r ↔ pullN (2+h) f∈familySpace (2+h) r := by
  rw [fixedContractions_iff,contraction_degree_reflection]

instance fixedContractions_finite (r : Fin 4 → ℕ) :
    Module.Finite K (fixedContractions (K:=K) r) := by
  let f : fixedContractions (K:=K) r →ₗ[K] familySpace 2 r :=
    { toFun p := ⟨pullN 2 p.val,p.property⟩
      map_add' _ _ := by apply Subtype.ext; simp
      map_smul' _ _ := by apply Subtype.ext; simp }
  apply Module.Finite.of_injective f
  intro p q hpq
  apply Subtype.ext
  apply pullN_injective 0
  exact congrArg Subtype.val hpq

theorem shiftI_smul (h : ℕ) (c : K) (f : P4 K) : shiftI h (c • f)=c • shiftI h f := by
  simp [shiftI,mul_smul_comm]

theorem shiftII_smul (h : ℕ) (c : K) (f : P4 K) : shiftII h (c • f)=c • shiftII h f := by
  simp [shiftII,mul_smul_comm]

theorem shiftI_fixedDegrees [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) (f : P4 K) :
    shiftI h f∈familySpaceEight (fun a => r a+degreeShiftI h a) ↔ f∈fixedContractions r := by
  rw [familySpaceEight_iff_euler,fixedContractions_iff]
  constructor
  · intro hp a
    apply typeI_map_injective h
    change shiftI h (eulerContraction a f)=shiftI h ((r a:K) • f)
    rw [shiftI_smul]
    have he := hp a
    rw [eulerEight_shiftI,Nat.cast_add,add_smul] at he
    exact add_right_cancel he
  · intro hp a
    rw [eulerEight_shiftI,hp a,shiftI_smul,Nat.cast_add,add_smul]

theorem shiftII_fixedDegrees [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) (f : P4 K) :
    shiftII h f∈familySpaceEight (fun a => r a+degreeShiftII h a) ↔ f∈fixedContractions r := by
  rw [familySpaceEight_iff_euler,fixedContractions_iff]
  constructor
  · intro hp a
    apply typeII_map_injective h
    change shiftII h (eulerContraction a f)=shiftII h ((r a:K) • f)
    rw [shiftII_smul]
    have he := hp a
    rw [eulerEight_shiftII,Nat.cast_add,add_smul] at he
    exact add_right_cancel he
  · intro hp a
    rw [eulerEight_shiftII,hp a,shiftII_smul,Nat.cast_add,add_smul]

def fixedRelativeI (h : ℕ) (r : Fin 4 → ℕ) : Submodule K (P8 K) :=
  familySpaceEight (fun a => r a+degreeShiftI h a) ⊓ relativeSpaceI h

def fixedRelativeII (h : ℕ) (r : Fin 4 → ℕ) : Submodule K (P8 K) :=
  familySpaceEight (fun a => r a+degreeShiftII h a) ⊓ relativeSpaceII h

def fixedGLContractionEquiv [Infinite K] [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) :
    fixedContractions (K:=K) r ≃ₗ[K] fixedGLInvariants (K:=K) (2+h) r where
  toFun f := ⟨pullN (2+h) f.val,
    (fixedContractions_rank h r f.val).mp f.property,pullN_gl_invariant (2+h) f.val⟩
  invFun p := ⟨covBackN h p.val,by
    apply (fixedContractions_rank h r _).mpr
    rw [← gl_invariant_reconstruction h p.val p.property.2]
    exact p.property.1⟩
  left_inv f := by apply Subtype.ext; exact covBackN_pullN h f.val
  right_inv p := by apply Subtype.ext; exact (gl_invariant_reconstruction h p.val p.property.2).symm
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

def fixedTypeIEquiv [Infinite K] [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) :
    fixedContractions (K:=K) r ≃ₗ[K] fixedRelativeI (K:=K) h r where
  toFun f := ⟨shiftI h f.val,(shiftI_fixedDegrees h r f.val).mpr f.property,shiftI_relative h f.val⟩
  invFun p := ⟨covBack p.val,by
    apply (shiftI_fixedDegrees h r _).mp
    rw [← relativeInvariantI_reconstruction h p.val p.property.2]
    exact p.property.1⟩
  left_inv f := by apply Subtype.ext; exact covBack_shiftI h f.val
  right_inv p := by apply Subtype.ext; exact (relativeInvariantI_reconstruction h p.val p.property.2).symm
  map_add' _ _ := by apply Subtype.ext; simp [shiftI,mul_add]
  map_smul' _ _ := by apply Subtype.ext; exact shiftI_smul _ _ _

def fixedTypeIIEquiv [Infinite K] [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) :
    fixedContractions (K:=K) r ≃ₗ[K] fixedRelativeII (K:=K) h r where
  toFun f := ⟨shiftII h f.val,(shiftII_fixedDegrees h r f.val).mpr f.property,shiftII_relative h f.val⟩
  invFun p := ⟨evalBack p.val,by
    apply (shiftII_fixedDegrees h r _).mp
    rw [← relativeInvariantII_reconstruction h p.val p.property.2]
    exact p.property.1⟩
  left_inv f := by apply Subtype.ext; exact evalBack_shiftII h f.val
  right_inv p := by apply Subtype.ext; exact (relativeInvariantII_reconstruction h p.val p.property.2).symm
  map_add' _ _ := by apply Subtype.ext; simp [shiftII,mul_add]
  map_smul' _ _ := by apply Subtype.ext; exact shiftII_smul _ _ _

/-- Both determinant maps are actual linear bijections on the complete fixed-degree
invariant spaces, not just injections on a chosen spanning collection. -/
def classicalRankReductionI [Infinite K] [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) :
    fixedGLInvariants (K:=K) (2+h) r ≃ₗ[K] fixedRelativeI (K:=K) h r :=
  (fixedGLContractionEquiv h r).symm.trans (fixedTypeIEquiv h r)

def classicalRankReductionII [Infinite K] [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) :
    fixedGLInvariants (K:=K) (2+h) r ≃ₗ[K] fixedRelativeII (K:=K) h r :=
  (fixedGLContractionEquiv h r).symm.trans (fixedTypeIIEquiv h r)

end AMSPhysical

#print axioms AMSPhysical.classicalRankReductionI
#print axioms AMSPhysical.classicalRankReductionII

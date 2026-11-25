import HighestFunctionalCartan
import PositiveHighestVertexUnique
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {q : ℝ} {n : ℕ}

def actualVertexAction (hq : q≠0) (A B : ActualIrrep q n) :=
  typeATensorRepresentation q hq n (fixedActualCarrier A).frame.action (fixedActualCarrier B).frame.action

def actualVertexPair (A B : ActualIrrep q n) :=
  LinearMap.BilinForm.tmul (fixedActualCarrier A).frame.pairing (fixedActualCarrier B).frame.pairing

def actualVertexBoundary (Λ : (B : ActualIrrep q n) → (fixedActualCarrier B).space →ₗ[ℝ] ℝ)
    (A B : ActualIrrep q n) :=
  (Λ B).comp (tensorFirstFunctional ((fixedActualCarrier A).frame.pairing (fixedActualCarrier A).frame.highest))

/-- Every index is an actual Dynkin weight. No construction, family, or
exterior quadruple is part of the vertex index. -/
def ActualPositiveVertex (hq : q≠0)
    (Λ : (B : ActualIrrep q n) → (fixedActualCarrier B).space →ₗ[ℝ] ℝ)
    (A B C : ActualIrrep q n)
    (F : (fixedActualCarrier C).space →ₗ[ℝ]
      (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space) : Prop :=
  (∀ z v,F ((fixedActualCarrier C).frame.action z v)=actualVertexAction hq A B z (F v)) ∧
  actualVertexPair A B (F (fixedActualCarrier C).frame.highest) (F (fixedActualCarrier C).frame.highest)=1 ∧
  0<actualVertexBoundary Λ A B (F (fixedActualCarrier C).frame.highest)

def actualPositiveVertexTable (hq : q≠0)
    (Λ : (B : ActualIrrep q n) → (fixedActualCarrier B).space →ₗ[ℝ] ℝ)
    (A B C : ActualIrrep q n) :
    (fixedActualCarrier C).space →ₗ[ℝ] (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space := by
  classical
  exact if h : ∃ F,ActualPositiveVertex hq Λ A B C F then Classical.choose h else 0

theorem actualPositiveVertexTable_spec (hq : q≠0)
    (Λ : (B : ActualIrrep q n) → (fixedActualCarrier B).space →ₗ[ℝ] ℝ)
    (A B C : ActualIrrep q n) (h : ∃ F,ActualPositiveVertex hq Λ A B C F) :
    ActualPositiveVertex hq Λ A B C (actualPositiveVertexTable hq Λ A B C) := by
  classical
  unfold actualPositiveVertexTable
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem actualPositiveVertexTable_eq (hq : q≠0)
    (Λ : (B : ActualIrrep q n) → (fixedActualCarrier B).space →ₗ[ℝ] ℝ)
    (A B C : ActualIrrep q n)
    (hLine : Module.finrank ℝ (typeAHighestSpace q n (actualVertexAction hq A B) C.val)=1)
    (F : (fixedActualCarrier C).space →ₗ[ℝ]
      (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space)
    (hF : ActualPositiveVertex hq Λ A B C F) : actualPositiveVertexTable hq Λ A B C=F := by
  have hT:=actualPositiveVertexTable_spec hq Λ A B C ⟨F,hF⟩
  exact (fixedActualCarrier C).frame.positive_full_intertwiner_unique
    (fixedActualCarrier C).complete (actualVertexAction hq A B) hLine
    (actualVertexPair A B) (actualVertexBoundary Λ A B)
    (actualPositiveVertexTable hq Λ A B C) F hT.1 hF.1 hT.2.1 hF.2.1 hT.2.2 hF.2.2

/-- In a multiplicity-free triple all positive constructions select exactly
the same entry of the single table, including coincident descriptions. -/
theorem actualPositiveVertex_alias_coherence (hq : q≠0)
    (Λ : (B : ActualIrrep q n) → (fixedActualCarrier B).space →ₗ[ℝ] ℝ)
    (A B C : ActualIrrep q n)
    (hLine : Module.finrank ℝ (typeAHighestSpace q n (actualVertexAction hq A B) C.val)=1)
    (F G : (fixedActualCarrier C).space →ₗ[ℝ]
      (fixedActualCarrier A).space ⊗[ℝ] (fixedActualCarrier B).space)
    (hF : ActualPositiveVertex hq Λ A B C F) (hG : ActualPositiveVertex hq Λ A B C G) : F=G :=
  (actualPositiveVertexTable_eq hq Λ A B C hLine F hF).symm.trans
    (actualPositiveVertexTable_eq hq Λ A B C hLine G hG)

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertex_alias_coherence

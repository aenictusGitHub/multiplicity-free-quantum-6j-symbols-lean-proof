import FullHighestEmbeddingCoherence
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- A complete actual finite-dimensional highest carrier. The object
label is its actual Dynkin weight, not a construction or family tag. -/
structure ActualHighestCarrier (q : ℝ) (n : ℕ) (lam : Fin n → ℤ) where
  space : ModuleCat.{0} ℝ
  frame : CompactHighestRealization q n space lam
  complete : frame.channel=⊤
  finite : Module.Finite ℝ space

def ActualHighestCarrier.ofWhole {V : Type} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (X : CompactHighestRealization q n V lam) (hX : X.channel=⊤) :
    ActualHighestCarrier q n lam where
  space := ModuleCat.of ℝ V
  frame := X
  complete := hX
  finite := inferInstance

def ActualHighestCarrier.ofChannel {V : Type} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (X : CompactHighestRealization q n V lam) :
    ActualHighestCarrier q n lam :=
  ofWhole X.onChannel X.onChannel_complete

/-- Two constructions of the same actual weight define the same object;
the existence witness is a proposition and cannot retain a family tag. -/
def ActualIrrep (q : ℝ) (n : ℕ) := {lam : Fin n → ℤ // Nonempty (ActualHighestCarrier q n lam)}

def ActualHighestCarrier.irrep {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (C : ActualHighestCarrier q n lam) : ActualIrrep q n := ⟨lam,⟨C⟩⟩

theorem ActualHighestCarrier.irrep_eq_of_weight {q : ℝ} {n : ℕ} {lam mu : Fin n → ℤ}
    (C : ActualHighestCarrier q n lam) (D : ActualHighestCarrier q n mu) (h : lam=mu) :
    C.irrep=D.irrep := Subtype.ext h

def fixedActualCarrier {q : ℝ} {n : ℕ} (A : ActualIrrep q n) : ActualHighestCarrier q n A.val :=
  Classical.choice A.property

def ActualHighestCarrier.mapTo {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C D : ActualHighestCarrier q n lam) : C.space →ₗ[ℝ] D.space :=
  C.frame.fullEmbedding hq C.complete D.frame

theorem ActualHighestCarrier.mapTo_self {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C : ActualHighestCarrier q n lam) : C.mapTo hq C=LinearMap.id :=
  C.frame.fullEmbedding_self hq C.complete

theorem ActualHighestCarrier.mapTo_comp {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C D E : ActualHighestCarrier q n lam) :
    (D.mapTo hq E).comp (C.mapTo hq D)=C.mapTo hq E :=
  C.frame.fullEmbedding_comp hq C.complete D.frame D.complete E.frame

theorem ActualHighestCarrier.mapTo_highest {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C D : ActualHighestCarrier q n lam) : C.mapTo hq D C.frame.highest=D.frame.highest :=
  C.frame.fullEmbedding_highest hq C.complete D.frame

theorem ActualHighestCarrier.mapTo_isometry {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C D : ActualHighestCarrier q n lam) (v w : C.space) :
    D.frame.pairing (C.mapTo hq D v) (C.mapTo hq D w)=C.frame.pairing v w :=
  C.frame.fullEmbedding_isometry hq C.complete D.frame v w

theorem ActualHighestCarrier.mapTo_intertwines {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C D : ActualHighestCarrier q n lam) (z : UqTypeA q n) (v : C.space) :
    C.mapTo hq D (C.frame.action z v)=D.frame.action z (C.mapTo hq D v) :=
  C.frame.fullEmbedding_intertwines hq C.complete D.frame z v

end AMSPhysical
#print axioms AMSPhysical.ActualHighestCarrier.mapTo_comp

import QuantumSL2
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

/-- The defining relations of U_q(sl_2), before taking their ring quotient.
The four generators are E, F, K, and K inverse, in that order. -/
inductive QuantumSL2Relation (q : K) : FreeAlgebra K (Fin 4) → FreeAlgebra K (Fin 4) → Prop
  | inverse : QuantumSL2Relation q (FreeAlgebra.ι K 2*FreeAlgebra.ι K 3) 1
  | inverse' : QuantumSL2Relation q (FreeAlgebra.ι K 3*FreeAlgebra.ι K 2) 1
  | weightE : QuantumSL2Relation q (FreeAlgebra.ι K 2*FreeAlgebra.ι K 0)
      (q^2 • (FreeAlgebra.ι K 0*FreeAlgebra.ι K 2))
  | weightF : QuantumSL2Relation q (FreeAlgebra.ι K 2*FreeAlgebra.ι K 1)
      (q^(-2:ℤ) • (FreeAlgebra.ι K 1*FreeAlgebra.ι K 2))
  | commutator : QuantumSL2Relation q
      (FreeAlgebra.ι K 0*FreeAlgebra.ι K 1-FreeAlgebra.ι K 1*FreeAlgebra.ι K 0)
      ((q-q⁻¹)⁻¹ • (FreeAlgebra.ι K 2-FreeAlgebra.ι K 3))

/-- An independently defined quantum enveloping algebra, not a definition by a 6j formula. -/
abbrev UqSL2 (q : K) := RingQuot (QuantumSL2Relation q)

def quantumFreeRepresentation (q : K) (l : ℤ) :
    FreeAlgebra K (Fin 4) →ₐ[K] Module.End K (WeightModule K) :=
  FreeAlgebra.lift K ![quantumE q,quantumF q l,quantumK q l,quantumKinv q l]

theorem quantumFree_respects (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℤ)
    {x y : FreeAlgebra K (Fin 4)} (h : QuantumSL2Relation q x y) :
    quantumFreeRepresentation q l x=quantumFreeRepresentation q l y := by
  cases h
  · simpa [quantumFreeRepresentation] using quantumK_inverse q hq l
  · simpa [quantumFreeRepresentation] using quantumKinv_inverse q hq l
  · simpa [quantumFreeRepresentation] using quantumK_E q hq l
  · simpa [quantumFreeRepresentation] using quantumK_F q hq l
  · simpa [quantumFreeRepresentation] using quantum_commutator q hq hden l

/-- A genuine representation of the presented quantum group on the explicit weight module. -/
def quantumRepresentation (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℤ) :
    UqSL2 q →ₐ[K] Module.End K (WeightModule K) :=
  RingQuot.liftAlgHom K ⟨quantumFreeRepresentation q l,by
    intro x y h
    exact quantumFree_respects q hq hden l h⟩

theorem quantumRepresentation_generator (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l : ℤ)
    (i : Fin 4) :
    quantumRepresentation q hq hden l (RingQuot.mkAlgHom K (QuantumSL2Relation q) (FreeAlgebra.ι K i))=
      ![quantumE q,quantumF q l,quantumK q l,quantumKinv q l] i := by
  simp [quantumRepresentation,RingQuot.liftAlgHom_mkAlgHom_apply,quantumFreeRepresentation]

end AMSPhysical

#print axioms AMSPhysical.quantumRepresentation

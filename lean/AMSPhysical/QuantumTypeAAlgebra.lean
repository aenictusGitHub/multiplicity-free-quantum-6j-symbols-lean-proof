import QuantumTypeASerre
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def typeAFreeGenerator (n : ℕ) (i : Fin n) (t : Fin 4) : FreeAlgebra K (Fin n×Fin 4) :=
  FreeAlgebra.ι K (i,t)

local notation "G" => typeAFreeGenerator (K:=K)

/-- The complete standard type-A quantum enveloping-algebra presentation.
The four generators at each simple root are E, F, K and K inverse. -/
inductive QuantumTypeARelation (q : K) (n : ℕ) :
    FreeAlgebra K (Fin n×Fin 4) → FreeAlgebra K (Fin n×Fin 4) → Prop
  | inverse (i : Fin n) : QuantumTypeARelation q n (G n i 2*G n i 3) 1
  | inverse' (i : Fin n) : QuantumTypeARelation q n (G n i 3*G n i 2) 1
  | torus (i j : Fin n) : QuantumTypeARelation q n (G n i 2*G n j 2) (G n j 2*G n i 2)
  | weightE (i j : Fin n) : QuantumTypeARelation q n (G n i 2*G n j 0)
      (q^(typeACartan n i j) • (G n j 0*G n i 2))
  | weightF (i j : Fin n) : QuantumTypeARelation q n (G n i 2*G n j 1)
      (q^(-typeACartan n i j) • (G n j 1*G n i 2))
  | commutator (i : Fin n) : QuantumTypeARelation q n
      (G n i 0*G n i 1-G n i 1*G n i 0) ((q-q⁻¹)⁻¹ • (G n i 2-G n i 3))
  | differentEF (i j : Fin n) (hij : i≠j) : QuantumTypeARelation q n (G n i 0*G n j 1) (G n j 1*G n i 0)
  | distantE (i j : Fin n) (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
      QuantumTypeARelation q n (G n i 0*G n j 0) (G n j 0*G n i 0)
  | distantF (i j : Fin n) (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
      QuantumTypeARelation q n (G n i 1*G n j 1) (G n j 1*G n i 1)
  | serreELeft (i j : Fin n) (hij : i.val+1=j.val) : QuantumTypeARelation q n
      (G n i 0*G n i 0*G n j 0-(q+q⁻¹) • (G n i 0*G n j 0*G n i 0)+G n j 0*G n i 0*G n i 0) 0
  | serreERight (i j : Fin n) (hij : i.val+1=j.val) : QuantumTypeARelation q n
      (G n j 0*G n j 0*G n i 0-(q+q⁻¹) • (G n j 0*G n i 0*G n j 0)+G n i 0*G n j 0*G n j 0) 0
  | serreFLeft (i j : Fin n) (hij : i.val+1=j.val) : QuantumTypeARelation q n
      (G n i 1*G n i 1*G n j 1-(q+q⁻¹) • (G n i 1*G n j 1*G n i 1)+G n j 1*G n i 1*G n i 1) 0
  | serreFRight (i j : Fin n) (hij : i.val+1=j.val) : QuantumTypeARelation q n
      (G n j 1*G n j 1*G n i 1-(q+q⁻¹) • (G n j 1*G n i 1*G n j 1)+G n i 1*G n j 1*G n j 1) 0

/-- Uq(sl_(n+1)) is defined independently by its standard relations. -/
abbrev UqTypeA (q : K) (n : ℕ) := RingQuot (QuantumTypeARelation q n)

def typeAFreeRepresentation (q : K) (n : ℕ) :
    FreeAlgebra K (Fin n×Fin 4) →ₐ[K] Module.End K (QuantumLatticeSpace K (Fin (n+1))) :=
  FreeAlgebra.lift K (fun it => ![typeAQuantumE q n it.1,typeAQuantumF q n it.1,
    typeAQuantumK q n it.1,typeAQuantumKi q n it.1] it.2)

theorem typeAFreeRepresentation_generator (q : K) (n : ℕ) (i : Fin n) (t : Fin 4) :
    typeAFreeRepresentation q n (G n i t)=
      ![typeAQuantumE q n i,typeAQuantumF q n i,typeAQuantumK q n i,typeAQuantumKi q n i] t := by
  simp [typeAFreeRepresentation,typeAFreeGenerator]

theorem typeAFreeRepresentation_respects (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    {x y : FreeAlgebra K (Fin n×Fin 4)} (h : QuantumTypeARelation q n x y) :
    typeAFreeRepresentation q n x=typeAFreeRepresentation q n y := by
  cases h with
  | inverse i => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_K_inverse q hq n i
  | inverse' i => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_Ki_inverse q hq n i
  | torus i j => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_K_commute q hq n i j
  | weightE i j => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_K_E q hq n i j
  | weightF i j => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_K_F q hq n i j
  | commutator i => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_EF_same q hq hD n i
  | differentEF i j hij => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_EF_different q n i j hij
  | distantE i j hd => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_E_distant q n i j hd
  | distantF i j hd => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_F_distant q n i j hd
  | serreELeft i j hij => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_E_serre_left q hq hD n i j hij
  | serreERight i j hij => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_E_serre_right q hq hD n i j hij
  | serreFLeft i j hij => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_F_serre_left q hq hD n i j hij
  | serreFRight i j hij => simpa [typeAFreeRepresentation,typeAFreeGenerator] using typeA_F_serre_right q hq hD n i j hij

/-- An actual representation of the independently presented arbitrary-rank
quantum enveloping algebra on occupation vectors. -/
def typeAQuantumRepresentation (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) :
    UqTypeA q n →ₐ[K] Module.End K (QuantumLatticeSpace K (Fin (n+1))) :=
  RingQuot.liftAlgHom K ⟨typeAFreeRepresentation q n,by intro x y h;exact typeAFreeRepresentation_respects q hq hD n h⟩

theorem typeAQuantumRepresentation_generator (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    (i : Fin n) (t : Fin 4) :
    typeAQuantumRepresentation q hq hD n (RingQuot.mkAlgHom K (QuantumTypeARelation q n) (G n i t))=
      ![typeAQuantumE q n i,typeAQuantumF q n i,typeAQuantumK q n i,typeAQuantumKi q n i] t := by
  simp [typeAQuantumRepresentation,typeAFreeRepresentation,typeAFreeGenerator]

end AMSPhysical

#print axioms AMSPhysical.typeAQuantumRepresentation

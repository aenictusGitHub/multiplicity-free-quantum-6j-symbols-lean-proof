import BalancedSL
import Mathlib.RingTheory.MvPolynomial.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def familyExponentSet (n : ℕ) (r : Fin 4 → ℕ) : Set (Fin 4×Fin n →₀ ℕ) :=
  {m | ∀ a,∑ i : Fin n,m (a,i)=r a}

/-- Actual fixed multidegrees in the four exterior tensor factors. -/
def familySpace (n : ℕ) (r : Fin 4 → ℕ) : Submodule K (PN K n) :=
  restrictSupport K (familyExponentSet n r)

theorem mem_familySpace (n : ℕ) (r : Fin 4 → ℕ) (p : PN K n) :
    p∈familySpace n r ↔ ∀ m∈p.support,∀ a,∑ i : Fin n,m (a,i)=r a := by
  rfl

theorem familySpace_familyDegrees (n : ℕ) (r : Fin 4 → ℕ) (p : PN K n)
    (hp : p∈familySpace n r) : HasFamilyDegrees n (fun a => (r a:ℤ)) p := by
  intro m hm a
  have he := hp hm a
  change ∑ i : Fin n,(m (a,i):ℤ)=(r a:ℤ)
  rw [← Nat.cast_sum,he]

theorem familySpace_degree_bound (n : ℕ) (r : Fin 4 → ℕ) :
    familySpace (K:=K) n r ≤ restrictDegree (Fin 4×Fin n) K (∑ a,r a) := by
  intro p hp
  apply (mem_restrictDegree (R:=K) (Fin 4×Fin n) p _).mpr
  intro m hm ⟨a,i⟩
  have h₁ : m (a,i)≤∑ j : Fin n,m (a,j) :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (m (a,j))) (Finset.mem_univ i)
  have h₂ : r a≤∑ b,r b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le (r b)) (Finset.mem_univ a)
  rw [hp hm a] at h₁
  exact h₁.trans h₂

instance familySpace_finite (n : ℕ) (r : Fin 4 → ℕ) : Module.Finite K (familySpace (K:=K) n r) := by
  let f := Submodule.inclusion (familySpace_degree_bound (K:=K) n r)
  exact Module.Finite.of_injective f (Submodule.inclusion_injective _)

def specialLinearSpace (n : ℕ) : Submodule K (PN K n) where
  carrier := {p | IsSpecialLinearInvariant n p}
  zero_mem' := by intro g hdet v; simp
  add_mem' := by intro p q hp hq g hdet v; simp only [map_add,hp g hdet v,hq g hdet v]
  smul_mem' := by
    intro c p hp g hdet v
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C,hp g hdet v]

def fixedGLInvariants (n : ℕ) (r : Fin 4 → ℕ) : Submodule K (PN K n) :=
  familySpace n r ⊓ (glInvariantAlgebra n).toSubmodule

def fixedSLInvariants (n : ℕ) (r : Fin 4 → ℕ) : Submodule K (PN K n) :=
  familySpace n r ⊓ specialLinearSpace n

instance fixedGLInvariants_finite (n : ℕ) (r : Fin 4 → ℕ) :
    Module.Finite K (fixedGLInvariants (K:=K) n r) := by
  let f := Submodule.inclusion (show fixedGLInvariants (K:=K) n r≤familySpace n r from inf_le_left)
  exact Module.Finite.of_injective f (Submodule.inclusion_injective _)

instance fixedSLInvariants_finite (n : ℕ) (r : Fin 4 → ℕ) :
    Module.Finite K (fixedSLInvariants (K:=K) n r) := by
  let f := Submodule.inclusion (show fixedSLInvariants (K:=K) n r≤familySpace n r from inf_le_left)
  exact Module.Finite.of_injective f (Submodule.inclusion_injective _)

theorem fixed_sl_eq_gl [IsAlgClosed K] (n : ℕ) (hn : 0<n) (r : Fin 4 → ℕ)
    (hbal : r 0+r 1=r 2+r 3) : fixedSLInvariants (K:=K) n r=fixedGLInvariants n r := by
  ext p
  constructor
  · intro hp
    refine ⟨hp.1,?_⟩
    apply balanced_sl_invariant_is_gl n hn p hp.2
    have hw := family_degrees_charge n (fun a => (r a:ℤ)) p
      (familySpace_familyDegrees n r p hp.1)
    have hz : (r 0:ℤ)+r 1-r 2-r 3=0 := by omega
    simpa [hz] using hw
  · intro hp
    refine ⟨hp.1,?_⟩
    intro g _ v
    exact hp.2 g v

end AMSPhysical

#print axioms AMSPhysical.fixed_sl_eq_gl

import QuantumCoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def IsQuantumIntertwiner (q : K) (A : UqSL2 q →ₐ[K] Module.End K V)
    (B : UqSL2 q →ₐ[K] Module.End K W) (T : V →ₗ[K] W) : Prop :=
  ∀ x v,B x (T v)=T (A x v)

theorem quantumIntertwiner_of_generators (q : K) (A : UqSL2 q →ₐ[K] Module.End K V)
    (B : UqSL2 q →ₐ[K] Module.End K W) (T : V →ₗ[K] W)
    (h : ∀ i v,B (uqGenerator q i) (T v)=T (A (uqGenerator q i) v)) :
    IsQuantumIntertwiner q A B T := by
  intro x
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (QuantumSL2Relation q) x
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro v
    simp only [AlgHom.commutes,Algebra.algebraMap_eq_smul_one,LinearMap.smul_apply,
      Module.End.one_apply,map_smul,map_one]
  | grade1 i => exact h i
  | mul a b ha hb =>
    intro v
    simp only [map_mul,Module.End.mul_apply,hb,ha]
  | add a b ha hb =>
    intro v
    simp only [map_add,LinearMap.add_apply,ha,hb]

theorem quantumKinv_intertwining (q : K) (A : UqSL2 q →ₐ[K] Module.End K V)
    (B : UqSL2 q →ₐ[K] Module.End K W) (T : V →ₗ[K] W)
    (h : ∀ v,B (uqGenerator q 2) (T v)=T (A (uqGenerator q 2) v)) (v : V) :
    B (uqGenerator q 3) (T v)=T (A (uqGenerator q 3) v) := by
  have hB (w : W) : B (uqGenerator q 3) (B (uqGenerator q 2) w)=w := by
    rw [← Module.End.mul_apply,← map_mul,uq_inverse',map_one,Module.End.one_apply]
  have hA (u : V) : A (uqGenerator q 2) (A (uqGenerator q 3) u)=u := by
    rw [← Module.End.mul_apply,← map_mul,uq_inverse,map_one,Module.End.one_apply]
  have he := congrArg (B (uqGenerator q 3)) (h (A (uqGenerator q 3) v))
  change B (uqGenerator q 3) (B (uqGenerator q 2) (T (A (uqGenerator q 3) v)))=
    B (uqGenerator q 3) (T (A (uqGenerator q 2) (A (uqGenerator q 3) v))) at he
  rw [hB,hA] at he
  exact he.symm

end AMSPhysical

#print axioms AMSPhysical.quantumIntertwiner_of_generators

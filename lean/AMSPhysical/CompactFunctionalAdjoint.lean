import CompactTypeAPair
import QuantumTypeAVectorInvariant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The actual compact adjoint of an invariant functional is an invariant
vector. This is proved for the displayed generators and then the entire
presented algebra, without an assumed abstract rigid category. -/
theorem compact_invariantFunctional_adjoint_vector (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hCompact : IsCompactTypeAPair q n B ρ) (hDef : ∀ x,B x x=0 → x=0)
    (f : V →ₗ[ℝ] ℝ) (C : V) (hPair : ∀ w,B C w=f w)
    (hInv : ∀ z : UqTypeA q n,∀ w,f (ρ z w)=typeAQuantumCounit q n z*f w) :
    ∀ z : UqTypeA q n,ρ z C=typeAQuantumCounit q n z • C := by
  apply typeA_invariantVector_of_generators q n ρ C
  intro i t
  fin_cases t
  · simp [typeAQuantumCounit_generator]
    apply hDef
    rw [hCompact.adjE i,hPair]
    change f (ρ (typeAAlgebraGenerator q n i 2) (ρ (typeAAlgebraGenerator q n i 1)
      (ρ (typeAAlgebraGenerator q n i 0) C)))=0
    rw [← Module.End.mul_apply,← map_mul,hInv]
    simp [map_mul,typeAQuantumCounit_generator]
  · simp [typeAQuantumCounit_generator]
    apply hDef
    rw [hCompact.adjF i,hPair]
    change f (ρ (typeAAlgebraGenerator q n i 0) (ρ (typeAAlgebraGenerator q n i 3)
      (ρ (typeAAlgebraGenerator q n i 1) C)))=0
    rw [← Module.End.mul_apply,← map_mul,hInv]
    simp [map_mul,typeAQuantumCounit_generator]
  · simp [typeAQuantumCounit_generator]
    apply sub_eq_zero.mp
    apply hDef
    rw [map_sub B,LinearMap.sub_apply,hCompact.adjK i,hPair,hPair,hInv]
    simp [typeAQuantumCounit_generator]
  · simp [typeAQuantumCounit_generator]
    apply sub_eq_zero.mp
    apply hDef
    rw [map_sub B,LinearMap.sub_apply,hCompact.adjKi i,hPair,hPair,hInv]
    simp [typeAQuantumCounit_generator]

end AMSPhysical

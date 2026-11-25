import FixedSameCasimir
import FockHilbert
import FockEight
import HilbertMatrixReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open MvPolynomial
open scoped ComplexOrder

attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

instance fixedRelativeI_finite (h : ℕ) (r : Fin 4 → ℕ) :
    Module.Finite ℂ (fixedRelativeI (K:=ℂ) h r) :=
  Module.Finite.of_injective (fixedTypeIEquiv h r).symm.toLinearMap (fixedTypeIEquiv h r).symm.injective

instance fixedRelativeII_finite (h : ℕ) (r : Fin 4 → ℕ) :
    Module.Finite ℂ (fixedRelativeII (K:=ℂ) h r) :=
  Module.Finite.of_injective (fixedTypeIIEquiv h r).symm.toLinearMap (fixedTypeIIEquiv h r).symm.injective

theorem glXYEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (glXYEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (glXYEnd h r p).val q.val=fock p.val (glXYEnd h r q).val
  rw [glXYEnd_val,glXYEnd_val]
  exact mixed_pair_fock_selfadjoint (2+h) 0 2 p.val q.val

theorem glZYEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (glZYEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (glZYEnd h r p).val q.val=fock p.val (glZYEnd h r q).val
  rw [glZYEnd_val,glZYEnd_val]
  exact mixed_pair_fock_selfadjoint (2+h) 1 2 p.val q.val

theorem glXXEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (glXXEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (glXXEnd h r p).val q.val=fock p.val (glXXEnd h r q).val
  rw [glXXEnd_val,glXXEnd_val]
  exact same_pair_fock_selfadjoint (2+h) 0 1 p.val q.val

theorem typeIXYEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (typeIXYEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (typeIXYEnd h r p).val q.val=fock p.val (typeIXYEnd h r q).val
  rw [typeIXYEnd_val,typeIXYEnd_val]
  exact mixedXYAmbient_fock_selfadjoint p.val q.val

theorem typeIZYEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (typeIZYEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (typeIZYEnd h r p).val q.val=fock p.val (typeIZYEnd h r q).val
  rw [typeIZYEnd_val,typeIZYEnd_val]
  exact mixedZYAmbient_fock_selfadjoint p.val q.val

theorem typeIIZYEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (typeIIZYEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (typeIIZYEnd h r p).val q.val=fock p.val (typeIIZYEnd h r q).val
  rw [typeIIZYEnd_val,typeIIZYEnd_val]
  exact mixedZYAmbient_fock_selfadjoint p.val q.val

theorem typeIIXXEnd_symmetric (h : ℕ) (r : Fin 4 → ℕ) : (typeIIXXEnd (K:=ℂ) h r).IsSymmetric := by
  intro p q
  change fock (typeIIXXEnd h r p).val q.val=fock p.val (typeIIXXEnd h r q).val
  rw [typeIIXXEnd_val,typeIIXXEnd_val]
  have hm (f : P8 ℂ) : (h:P8 ℂ)*f=(h:ℂ) • f := by simp [Algebra.smul_def]
  rw [hm,hm,fock_add_left,fock_add_right,fock_smul_left,fock_smul_right,
    omegaXX_fock_selfadjoint]
  simp

/-- An actual unitary simultaneous intertwiner for both Type-I operators on complete
fixed-degree invariant spaces, with Fock norms and orthonormal bases constructed here. -/
theorem classicalTypeI_unitary (h : ℕ) (r : Fin 4 → ℕ) :
    ∃ n : ℕ,∃ v : OrthonormalBasis (Fin n) ℂ (fixedGLInvariants (K:=ℂ) (2+h) r),
      ∃ w : OrthonormalBasis (Fin n) ℂ (fixedRelativeI (K:=ℂ) h r),
        ∃ S : unitary (CStarMatrix (Fin n) (Fin n) ℂ),
          orthonormalMatrix n w (typeIXYEnd h r)*(S:CStarMatrix (Fin n) (Fin n) ℂ)=
            (S:CStarMatrix (Fin n) (Fin n) ℂ)*orthonormalMatrix n v (glXYEnd h r) ∧
          orthonormalMatrix n w (typeIZYEnd h r)*(S:CStarMatrix (Fin n) (Fin n) ℂ)=
            (S:CStarMatrix (Fin n) (Fin n) ℂ)*orthonormalMatrix n v (glZYEnd h r) := by
  let f := classicalRankReductionI (K:=ℂ) h r
  let n := Module.finrank ℂ (fixedGLInvariants (K:=ℂ) (2+h) r)
  let v := stdOrthonormalBasis ℂ (fixedGLInvariants (K:=ℂ) (2+h) r)
  let w := (stdOrthonormalBasis ℂ (fixedRelativeI (K:=ℂ) h r)).reindex (finCongr f.finrank_eq.symm)
  refine ⟨n,v,w,?_⟩
  exact finiteHilbert_simultaneous_unitary n v w f _ _ _ _
    (glXYEnd_symmetric h r) (glZYEnd_symmetric h r) (typeIXYEnd_symmetric h r) (typeIZYEnd_symmetric h r)
    (fun p => (rankReductionI_XY h r p).symm) (fun p => (rankReductionI_ZY h r p).symm)

theorem classicalTypeII_unitary (h : ℕ) (r : Fin 4 → ℕ) :
    ∃ n : ℕ,∃ v : OrthonormalBasis (Fin n) ℂ (fixedGLInvariants (K:=ℂ) (2+h) r),
      ∃ w : OrthonormalBasis (Fin n) ℂ (fixedRelativeII (K:=ℂ) h r),
        ∃ S : unitary (CStarMatrix (Fin n) (Fin n) ℂ),
          orthonormalMatrix n w (typeIIXXEnd h r)*(S:CStarMatrix (Fin n) (Fin n) ℂ)=
            (S:CStarMatrix (Fin n) (Fin n) ℂ)*orthonormalMatrix n v (glXXEnd h r) ∧
          orthonormalMatrix n w (typeIIZYEnd h r)*(S:CStarMatrix (Fin n) (Fin n) ℂ)=
            (S:CStarMatrix (Fin n) (Fin n) ℂ)*orthonormalMatrix n v (glZYEnd h r) := by
  let f := classicalRankReductionII (K:=ℂ) h r
  let n := Module.finrank ℂ (fixedGLInvariants (K:=ℂ) (2+h) r)
  let v := stdOrthonormalBasis ℂ (fixedGLInvariants (K:=ℂ) (2+h) r)
  let w := (stdOrthonormalBasis ℂ (fixedRelativeII (K:=ℂ) h r)).reindex (finCongr f.finrank_eq.symm)
  refine ⟨n,v,w,?_⟩
  exact finiteHilbert_simultaneous_unitary n v w f _ _ _ _
    (glXXEnd_symmetric h r) (glZYEnd_symmetric h r) (typeIIXXEnd_symmetric h r) (typeIIZYEnd_symmetric h r)
    (fun p => (rankReductionII_XX h r p).symm) (fun p => (rankReductionII_ZY h r p).symm)

end AMSPhysical

#print axioms AMSPhysical.classicalTypeI_unitary
#print axioms AMSPhysical.classicalTypeII_unitary

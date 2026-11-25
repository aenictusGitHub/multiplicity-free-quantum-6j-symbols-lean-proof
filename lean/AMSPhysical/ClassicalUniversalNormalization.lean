import UniversalFockNormalization
import FixedFockSpaces

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open MvPolynomial
open scoped ComplexOrder
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

theorem classicalRankReductionI_universal_metric (h : ℕ) (r : Fin 4 → ℕ)
    (p q : fixedGLInvariants (K:=ℂ) (2+h) r) :
    fock (classicalRankReductionI h r p).val (classicalRankReductionI h r q).val=
      ((h.factorial*(h+1).factorial:ℕ):ℂ)*fock p.val q.val := by
  let f := (fixedGLContractionEquiv (K:=ℂ) h r).symm p
  let g := (fixedGLContractionEquiv (K:=ℂ) h r).symm q
  change fock (shiftI h f.val) (shiftI h g.val)=_
  rw [shiftI_fock_universal]
  have hf:=congrArg Subtype.val ((fixedGLContractionEquiv (K:=ℂ) h r).apply_symm_apply p)
  have hg:=congrArg Subtype.val ((fixedGLContractionEquiv (K:=ℂ) h r).apply_symm_apply q)
  change pullN (2+h) f.val=p.val at hf
  change pullN (2+h) g.val=q.val at hg
  rw [hf,hg]

theorem classicalRankReductionII_universal_metric (h : ℕ) (r : Fin 4 → ℕ)
    (p q : fixedGLInvariants (K:=ℂ) (2+h) r) :
    fock (classicalRankReductionII h r p).val (classicalRankReductionII h r q).val=
      ((h.factorial*(h+1).factorial:ℕ):ℂ)*fock p.val q.val := by
  let f := (fixedGLContractionEquiv (K:=ℂ) h r).symm p
  let g := (fixedGLContractionEquiv (K:=ℂ) h r).symm q
  change fock (shiftII h f.val) (shiftII h g.val)=_
  rw [shiftII_fock_universal]
  have hf:=congrArg Subtype.val ((fixedGLContractionEquiv (K:=ℂ) h r).apply_symm_apply p)
  have hg:=congrArg Subtype.val ((fixedGLContractionEquiv (K:=ℂ) h r).apply_symm_apply q)
  change pullN (2+h) f.val=p.val at hf
  change pullN (2+h) g.val=q.val at hg
  rw [hf,hg]

def determinantUniversalScale (h : ℕ) : ℂ :=
  ((Real.sqrt ((h.factorial*(h+1).factorial:ℕ):ℝ))⁻¹ : ℝ)

theorem determinantUniversalScale_ne_zero (h : ℕ) : determinantUniversalScale h≠0 := by
  unfold determinantUniversalScale
  have hp : 0<((h.factorial*(h+1).factorial:ℕ):ℝ) := by positivity
  exact_mod_cast (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hp)))

theorem determinantUniversalScale_normalization (h : ℕ) :
    star (determinantUniversalScale h)*determinantUniversalScale h*
      ((h.factorial*(h+1).factorial:ℕ):ℂ)=1 := by
  let a : ℝ := Real.sqrt ((h.factorial*(h+1).factorial:ℕ):ℝ)
  have hp : 0<((h.factorial*(h+1).factorial:ℕ):ℝ) := by positivity
  have ha : a≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs : a*a=((h.factorial*(h+1).factorial:ℕ):ℝ) := by
    simpa only [pow_two] using Real.sq_sqrt hp.le
  have hcomplex : (a:ℂ)*(a:ℂ)=((h.factorial*(h+1).factorial:ℕ):ℂ) := by exact_mod_cast hs
  have hac : (a:ℂ)≠0 := by exact_mod_cast ha
  change star ((a⁻¹:ℝ):ℂ)*((a⁻¹:ℝ):ℂ)*_=1
  rw [show star ((a⁻¹:ℝ):ℂ)=((a⁻¹:ℝ):ℂ) by simp only [Complex.star_def,Complex.conj_ofReal]]
  simp only [Complex.ofReal_inv]
  rw [← hcomplex]
  field_simp

def classicalUniversalI (h : ℕ) (r : Fin 4 → ℕ) :
    fixedGLInvariants (K:=ℂ) (2+h) r ≃ₗ[ℂ] fixedRelativeI (K:=ℂ) h r :=
  (classicalRankReductionI h r).trans
    (LinearEquiv.smulOfNeZero ℂ (fixedRelativeI (K:=ℂ) h r)
      (determinantUniversalScale h) (determinantUniversalScale_ne_zero h))

def classicalUniversalII (h : ℕ) (r : Fin 4 → ℕ) :
    fixedGLInvariants (K:=ℂ) (2+h) r ≃ₗ[ℂ] fixedRelativeII (K:=ℂ) h r :=
  (classicalRankReductionII h r).trans
    (LinearEquiv.smulOfNeZero ℂ (fixedRelativeII (K:=ℂ) h r)
      (determinantUniversalScale h) (determinantUniversalScale_ne_zero h))

theorem classicalUniversalI_inner (h : ℕ) (r : Fin 4 → ℕ)
    (p q : fixedGLInvariants (K:=ℂ) (2+h) r) :
    inner ℂ (classicalUniversalI h r p) (classicalUniversalI h r q)=inner ℂ p q := by
  change fock (determinantUniversalScale h • (classicalRankReductionI h r p).val)
    (determinantUniversalScale h • (classicalRankReductionI h r q).val)=fock p.val q.val
  rw [fock_smul_left,fock_smul_right,classicalRankReductionI_universal_metric]
  calc
    _=(star (determinantUniversalScale h)*determinantUniversalScale h*
      ((h.factorial*(h+1).factorial:ℕ):ℂ))*fock p.val q.val := by ring
    _=fock p.val q.val := by rw [determinantUniversalScale_normalization,one_mul]

theorem classicalUniversalII_inner (h : ℕ) (r : Fin 4 → ℕ)
    (p q : fixedGLInvariants (K:=ℂ) (2+h) r) :
    inner ℂ (classicalUniversalII h r p) (classicalUniversalII h r q)=inner ℂ p q := by
  change fock (determinantUniversalScale h • (classicalRankReductionII h r p).val)
    (determinantUniversalScale h • (classicalRankReductionII h r q).val)=fock p.val q.val
  rw [fock_smul_left,fock_smul_right,classicalRankReductionII_universal_metric]
  calc
    _=(star (determinantUniversalScale h)*determinantUniversalScale h*
      ((h.factorial*(h+1).factorial:ℕ):ℂ))*fock p.val q.val := by ring
    _=fock p.val q.val := by rw [determinantUniversalScale_normalization,one_mul]

/-- Explicit isometry on the full physical classical invariant spaces,
with the universal scalar, without polar decomposition. -/
def classicalUniversalIsometryI (h : ℕ) (r : Fin 4 → ℕ) :
    fixedGLInvariants (K:=ℂ) (2+h) r ≃ₗᵢ[ℂ] fixedRelativeI (K:=ℂ) h r :=
  { classicalUniversalI h r with
    norm_map' := (LinearMap.norm_map_iff_inner_map_map (classicalUniversalI h r).toLinearMap).mpr
      (classicalUniversalI_inner h r) }

def classicalUniversalIsometryII (h : ℕ) (r : Fin 4 → ℕ) :
    fixedGLInvariants (K:=ℂ) (2+h) r ≃ₗᵢ[ℂ] fixedRelativeII (K:=ℂ) h r :=
  { classicalUniversalII h r with
    norm_map' := (LinearMap.norm_map_iff_inner_map_map (classicalUniversalII h r).toLinearMap).mpr
      (classicalUniversalII_inner h r) }

end AMSPhysical
#print axioms AMSPhysical.classicalUniversalIsometryI
#print axioms AMSPhysical.classicalUniversalIsometryII

import FixedEquivalences

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

theorem eval_unpackEight (p : P8 K) (v : Fin 8 → K) :
    eval (fun ai => v (finProdFinEquiv ai)) (unpackEight p)=eval v p := by
  simp [unpackEight,eval_rename,Function.comp_def]

theorem charge_unpackEight (ai : Fin 4×Fin 2) :
    vectorCovectorWeight (finProdFinEquiv ai)=familyCharge 2 ai := by
  obtain ⟨a,i⟩ := ai
  fin_cases a <;> fin_cases i <;> rfl

theorem familyEight_scaling (r : Fin 4 → ℕ) (p : P8 K) (hp : p∈familySpaceEight r)
    (t : K) (ht : t≠0) (v : Fin 8 → K) :
    eval (weightScale vectorCovectorWeight t v) p=
      t^((r 0:ℤ)+r 1-r 2-r 3)*eval v p := by
  have hd : unpackEight p∈familySpace 2 r := hp
  have hw := family_degrees_charge 2 (fun a => (r a:ℤ)) (unpackEight p)
    (familySpace_familyDegrees 2 r (unpackEight p) hd)
  rw [← eval_unpackEight p (weightScale vectorCovectorWeight t v)]
  have he : (fun ai => weightScale vectorCovectorWeight t v (finProdFinEquiv ai))=
      weightScale (familyCharge 2) t (fun ai => v (finProdFinEquiv ai)) := by
    funext ai
    dsimp only [weightScale]
    rw [charge_unpackEight ai]
  rw [he,eval_weightScale _ _ _ hw t ht,eval_unpackEight]

theorem relativeI_is_sl2 (h : ℕ) (p : P8 K) (hp : IsRelativeInvariantI h p) :
    IsSL2Invariant p := by
  intro a b c d hd v
  have he := hp a b c d (by rw [hd]; exact one_ne_zero) v
  simpa [hd] using he

theorem relativeII_is_sl2 (h : ℕ) (p : P8 K) (hp : IsRelativeInvariantII h p) :
    IsSL2Invariant p := by
  intro a b c d hd v
  have he := hp a b c d (by rw [hd]; exact one_ne_zero) v
  simpa [hd] using he

theorem sl2_fixed_relativeI [IsAlgClosed K] (h : ℕ) (r : Fin 4 → ℕ) (p : P8 K)
    (hbal : r 0+r 1=r 2+r 3)
    (hd : p∈familySpaceEight (fun a => r a+degreeShiftI h a)) (hp : IsSL2Invariant p) :
    IsRelativeInvariantI h p := by
  intro a b c d hD v
  obtain ⟨t,hts⟩ := IsAlgClosed.exists_pow_nat_eq (det2 a b c d) (by norm_num : 0<2)
  have ht : t≠0 := by intro hz; rw [hz] at hts; simp at hts; exact hD hts.symm
  rw [twoAction_normalize a b c d t ht hts,familyEight_scaling _ p hd t ht]
  rw [hp (a/t) (b/t) (c/t) (d/t) (normalized_det a b c d t ht hts)]
  have he : ((r 0+degreeShiftI h 0:ℕ):ℤ)+((r 1+degreeShiftI h 1:ℕ):ℤ)-
      ((r 2+degreeShiftI h 2:ℕ):ℤ)-((r 3+degreeShiftI h 3:ℕ):ℤ)=-(2*(h:ℤ)) := by
    simp only [degreeShiftI,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons]
    omega
  rw [he,← hts,← pow_mul]
  have hc : ((2*h:ℕ):ℤ)=2*(h:ℤ) := by omega
  rw [← hc,zpow_neg,zpow_natCast]
  field_simp

theorem sl2_fixed_relativeII [IsAlgClosed K] (h : ℕ) (r : Fin 4 → ℕ) (p : P8 K)
    (hbal : r 0+r 1=r 2+r 3)
    (hd : p∈familySpaceEight (fun a => r a+degreeShiftII h a)) (hp : IsSL2Invariant p) :
    IsRelativeInvariantII h p := by
  intro a b c d hD v
  obtain ⟨t,hts⟩ := IsAlgClosed.exists_pow_nat_eq (det2 a b c d) (by norm_num : 0<2)
  have ht : t≠0 := by intro hz; rw [hz] at hts; simp at hts; exact hD hts.symm
  rw [twoAction_normalize a b c d t ht hts,familyEight_scaling _ p hd t ht]
  rw [hp (a/t) (b/t) (c/t) (d/t) (normalized_det a b c d t ht hts)]
  have he : ((r 0+degreeShiftII h 0:ℕ):ℤ)+((r 1+degreeShiftII h 1:ℕ):ℤ)-
      ((r 2+degreeShiftII h 2:ℕ):ℤ)-((r 3+degreeShiftII h 3:ℕ):ℤ)=2*(h:ℤ) := by
    simp only [degreeShiftII,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons]
    omega
  rw [he,← hts,← pow_mul]
  congr 1
  norm_cast

def sl2PolynomialSpace : Submodule K (P8 K) where
  carrier := {p | IsSL2Invariant p}
  zero_mem' := by intro a b c d hd v; simp
  add_mem' := by intro p q hp hq a b c d hd v; simp [hp a b c d hd v,hq a b c d hd v]
  smul_mem' := by
    intro t p hp a b c d hd v
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C,hp a b c d hd v]

def fixedSL2Eight (r : Fin 4 → ℕ) : Submodule K (P8 K) :=
  familySpaceEight r ⊓ sl2PolynomialSpace

theorem fixedRelativeI_eq_sl2 [IsAlgClosed K] (h : ℕ) (r : Fin 4 → ℕ)
    (hbal : r 0+r 1=r 2+r 3) :
    fixedRelativeI (K:=K) h r=fixedSL2Eight (fun a => r a+degreeShiftI h a) := by
  ext p
  constructor
  · intro hp; exact ⟨hp.1,relativeI_is_sl2 h p hp.2⟩
  · intro hp; exact ⟨hp.1,sl2_fixed_relativeI h r p hbal hp.1 hp.2⟩

theorem fixedRelativeII_eq_sl2 [IsAlgClosed K] (h : ℕ) (r : Fin 4 → ℕ)
    (hbal : r 0+r 1=r 2+r 3) :
    fixedRelativeII (K:=K) h r=fixedSL2Eight (fun a => r a+degreeShiftII h a) := by
  ext p
  constructor
  · intro hp; exact ⟨hp.1,relativeII_is_sl2 h p hp.2⟩
  · intro hp; exact ⟨hp.1,sl2_fixed_relativeII h r p hbal hp.1 hp.2⟩

def classicalSLRankReductionI [Infinite K] [CharZero K] [IsAlgClosed K]
    (h : ℕ) (r : Fin 4 → ℕ) (hbal : r 0+r 1=r 2+r 3) :
    fixedSLInvariants (K:=K) (2+h) r ≃ₗ[K]
      fixedSL2Eight (K:=K) (fun a => r a+degreeShiftI h a) :=
  (LinearEquiv.ofEq _ _ (fixed_sl_eq_gl (2+h) (by omega) r hbal)).trans
    ((classicalRankReductionI h r).trans
      (LinearEquiv.ofEq _ _ (fixedRelativeI_eq_sl2 h r hbal)))

def classicalSLRankReductionII [Infinite K] [CharZero K] [IsAlgClosed K]
    (h : ℕ) (r : Fin 4 → ℕ) (hbal : r 0+r 1=r 2+r 3) :
    fixedSLInvariants (K:=K) (2+h) r ≃ₗ[K]
      fixedSL2Eight (K:=K) (fun a => r a+degreeShiftII h a) :=
  (LinearEquiv.ofEq _ _ (fixed_sl_eq_gl (2+h) (by omega) r hbal)).trans
    ((classicalRankReductionII h r).trans
      (LinearEquiv.ofEq _ _ (fixedRelativeII_eq_sl2 h r hbal)))

end AMSPhysical

#print axioms AMSPhysical.classicalSLRankReductionI
#print axioms AMSPhysical.classicalSLRankReductionII

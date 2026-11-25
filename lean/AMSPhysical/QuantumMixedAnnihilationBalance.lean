import QuantumOccupationUnitWeights
import QuantumMixedAnnihilationCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def mixedAnnihilationScale (q : ℝ) (n l m : ℕ) : ℝ :=
  q^((n:ℤ)-(l:ℤ)-(m:ℤ))/(qInteger q ((l:ℤ)+1)*qInteger q ((m:ℤ)+1))

theorem mixedAnnihilationScale_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ) :
    0<mixedAnnihilationScale q n l m := by
  unfold mixedAnnihilationScale
  apply div_pos (zpow_pos hq _)
  apply mul_pos
  · exact qInteger_pos_real q hq hq1 _ (by omega)
  · exact qInteger_pos_real q hq hq1 _ (by omega)

/-- Exact occupation coefficient balance between raw annihilation and
physical creation, with the independently constructed positive metrics. -/
theorem mixedAnnihilation_coefficient_balance (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l m : ℕ) (i : Fin (n+1))
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    mixedCreationCoefficient q n i (x.val,y.val)*
      (occupationCompactWeight q n (l+1) (shiftedOccupation n l 1 i x)*
        occupationOppositeWeight q n (m+1) (shiftedOccupation n m 1 i y))=
      mixedAnnihilationScale q n l m*
        mixedAnnihilationCoefficient q n i ((x.val,y.val)+mixedCreationShift n i)*
        (occupationCompactWeight q n l x*occupationOppositeWeight q n m y) := by
  rw [occupationCompactWeight_unit_shift q hq hq1,occupationOppositeWeight_unit_shift q hq hq1]
  unfold mixedCreationCoefficient mixedAnnihilationCoefficient mixedAnnihilationScale mixedCreationShift
  simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_eq_same,
    occupationStrictPrefix_add,occupationStrictPrefix_self_single,add_zero]
  rw [occupationPrefix_strict,occupationPrefix_strict]
  have hp : q^(-(i.val:ℤ)-(occupationStrictPrefix n i x.val+x.val i)-
        (occupationStrictPrefix n i y.val+y.val i))*
      (q^(x.val i-(l:ℤ)+(i.val:ℤ))*q^((n:ℤ)+y.val i-(m:ℤ)-(i.val:ℤ)))=
      q^((n:ℤ)-(l:ℤ)-(m:ℤ))*
        q^(-(i.val:ℤ)-occupationStrictPrefix n i x.val-occupationStrictPrefix n i y.val) := by
    simp only [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  calc
    _ = ((-1:ℝ)^i.val*qInteger q (x.val i+1)*qInteger q (y.val i+1)*
        occupationCompactWeight q n l x*occupationOppositeWeight q n m y/
        (qInteger q ((l:ℤ)+1)*qInteger q ((m:ℤ)+1)))*
        (q^(-(i.val:ℤ)-(occupationStrictPrefix n i x.val+x.val i)-
          (occupationStrictPrefix n i y.val+y.val i))*
          (q^(x.val i-(l:ℤ)+(i.val:ℤ))*q^((n:ℤ)+y.val i-(m:ℤ)-(i.val:ℤ)))) := by ring
    _ = _ := by rw [hp];ring

end AMSPhysical

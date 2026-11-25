import QuantumOccupationShiftNorm
import QuantumReflectionMetric
import QuantumLatticeReflectSingle

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem shiftedOccupation_factorial_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l : ℕ) (k : Fin (n+1)) (x : occupationWeights (Fin (n+1)) l) :
    occupationFactorialProduct q n (l+1) (shiftedOccupation n l 1 k x)=
      qInteger q (x.val k+1)*occupationFactorialProduct q n l x := by
  have h:=shiftedOccupation_factorials q n l 1 k x
  rw [qfactorial_succ] at h
  have hqk : qnum q ((x.val k).toNat+1)=qInteger q (x.val k+1) := by
    rw [qnum_eq_qInteger q hq hq1]
    simp only [Nat.cast_add,Nat.cast_one,Int.toNat_of_nonneg (x.property.1 k)]
  rw [hqk,mul_assoc] at h
  exact mul_left_cancel₀ (qfactorial_ne_zero q hq (x.val k).toNat) h

theorem qfactorial_succ_integer (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l : ℕ) :
    qfactorial q (l+1)=qfactorial q l*qInteger q ((l:ℤ)+1) := by
  rw [qfactorial_succ,qnum_eq_qInteger q hq hq1]
  simp only [Nat.cast_add,Nat.cast_one]

theorem occupationCompactWeight_unit_shift (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l : ℕ) (k : Fin (n+1)) (x : occupationWeights (Fin (n+1)) l) :
    occupationCompactWeight q n (l+1) (shiftedOccupation n l 1 k x)=
      (q^(x.val k-(l:ℤ)+(k.val:ℤ))*qInteger q (x.val k+1)/qInteger q ((l:ℤ)+1))*
        occupationCompactWeight q n l x := by
  unfold occupationCompactWeight
  rw [shiftedOccupation_energy,shiftedOccupation_heightZ,shiftedOccupation_factorial_unit q hq hq1,
    qfactorial_succ_integer q hq hq1]
  simp only [Nat.cast_one,one_mul,mul_one]
  have hp : q^(occupationEnergy n l x+(x.val k-(l:ℤ))+(occupationHeightZ n l x+(k.val:ℤ)))=
      q^(x.val k-(l:ℤ)+(k.val:ℤ))*q^(occupationEnergy n l x+occupationHeightZ n l x) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  rw [hp]
  field_simp

theorem occupationReflection_unit_shift (n l : ℕ) (k : Fin (n+1)) (x : occupationWeights (Fin (n+1)) l) :
    occupationReflection n (l+1) (shiftedOccupation n l 1 k x)=
      shiftedOccupation n l 1 k.rev (occupationReflection n l x) := by
  apply Subtype.ext
  change occupationLatticeReflect n (x.val+Pi.single k 1)=occupationLatticeReflect n x.val+Pi.single k.rev 1
  rw [occupationLatticeReflect_add,occupationLatticeReflect_single]

theorem occupationOppositeWeight_unit_shift (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l : ℕ) (k : Fin (n+1)) (x : occupationWeights (Fin (n+1)) l) :
    occupationOppositeWeight q n (l+1) (shiftedOccupation n l 1 k x)=
      (q^((n:ℤ)+x.val k-(l:ℤ)-(k.val:ℤ))*qInteger q (x.val k+1)/qInteger q ((l:ℤ)+1))*
        occupationOppositeWeight q n l x := by
  rw [← occupationReflection_compact_weight q (ne_of_gt hq),occupationReflection_unit_shift,
    occupationCompactWeight_unit_shift q hq hq1,occupationReflection_compact_weight q (ne_of_gt hq)]
  have he : (occupationReflection n l x).val k.rev=x.val k := by change x.val k.rev.rev=x.val k;rw [Fin.rev_rev]
  rw [he]
  have hk : (k.rev.val:ℤ)=(n:ℤ)-(k.val:ℤ) := by have hh:=k.isLt;simp only [Fin.val_rev];omega
  rw [hk]
  have hp : x.val k-(l:ℤ)+((n:ℤ)-(k.val:ℤ))=(n:ℤ)+x.val k-(l:ℤ)-(k.val:ℤ) := by ring
  rw [hp]

end AMSPhysical

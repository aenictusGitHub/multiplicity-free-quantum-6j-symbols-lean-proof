import QuantumGaugeFactor
import FirstOrderGridUnique
import QuantumRacahUniqueness

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The finite product gauge has a closed quantum-factorial expression in
terms of the independently constructed coupling-vector norms. -/
theorem spinRacahGauge_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (first : FixedLeftHighest l m n H) (hb : first.val.1.val=0 ∨ first.val.2.val=n) :
    ∀ p : FixedLeftHighest l m n H,
      spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val=
        projectedLeftLeading q l m n p.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) p.val/
          (projectedLeftLeading q l m n first.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) first.val) := by
  have hbase : projectedLeftLeading q l m n first.val*
      projectedGaugeFactor q l m n (leftHighestDefect l m n H) first.val≠0 :=
    mul_ne_zero (ne_of_gt (projectedLeftLeading_pos q hq l m n first.val))
      (ne_of_gt (projectedGaugeFactor_pos q hq l m n _ first.val))
  have hprev : ∀ p : FixedLeftHighest l m n H,p≠first →
      ∃ v : FixedLeftHighest l m n H,v.val.1.val+1=p.val.1.val ∧
        sl2RacahDeath q l m n p.val.1.val p.val.2.val≠0 := by
    intro p hp
    obtain ⟨v,hv,_⟩ := quantumRacahJacobi_connected q hq hq1 l m n H first hb p hp
    refine ⟨v,hv,?_⟩
    intro hz
    have hs := quantumRacahJacobi_step_sq_rates q hq hq1 l m n H p v hv
    rw [hz,zero_mul] at hs
    exact (ne_of_gt (quantumRacahJacobi_step_pos q hq hq1 l m n H p v hv)) (sq_eq_zero_iff.mp hs)
  have he := first_order_grid_unique (fun p : FixedLeftHighest l m n H => p.val.1.val) first
    (fun p => sl2RacahDeath q l m n p.val.1.val p.val.2.val)
    (quantumRacahJacobi q hq hq1 l m n H) hprev
    (fun p => spinRacahGauge q l m n (leftHighestDefect l m n H) p.val.1.val)
    (fun p => projectedLeftLeading q l m n p.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) p.val/
      (projectedLeftLeading q l m n first.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) first.val))
    (spinRacahGauge_death q hq hq1 l m n H) ?_ ?_
  · exact fun p => congrFun he p
  · intro p v hv
    have hdv := ne_of_gt (projectedLeftLeading_pos q hq l m n v.val)
    have hz := projectedGaugeFactor_neighbor q hq hq1 l m n H p v hv
    calc
      _ = (projectedLeftLeading q l m n p.val/
        (projectedLeftLeading q l m n first.val*projectedGaugeFactor q l m n (leftHighestDefect l m n H) first.val))*
        (sl2RacahDeath q l m n p.val.1.val p.val.2.val*
          projectedGaugeFactor q l m n (leftHighestDefect l m n H) p.val) := by ring
      _ = _ := by
        rw [hz,quantumRacahJacobi_step q hq hq1 l m n H p v hv]
        field_simp [hdv,hbase]
  · have hidx := fixedLeftHighest_boundary_index l m n H first hb
    have hw : spinRacahGauge q l m n (leftHighestDefect l m n H) first.val.1.val=1 := by
      rw [hidx,spinRacahGauge_first]
    dsimp only
    rw [hw]
    exact (div_self hbase).symm

end AMSPhysical

#print axioms AMSPhysical.spinRacahGauge_closed

import QuantumStrictPrefix
import QuantumPrefixTelescoping
import QuantumPairRaising

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def mixedRadialDiagonalCoefficient (q : ℝ) (n : ℕ) (i : Fin (n+1)) (p : OccupationPairLattice n) : ℝ :=
  q^(-2*(i.val:ℤ)-2*occupationStrictPrefix n i p.1-2*occupationStrictPrefix n i p.2-p.1 i-p.2 i)*
    qInteger q (p.1 i+p.2 i+1)

/-- The full diagonal contraction commutator is evaluated by a proved
ordered quantum-geometric telescoping identity in arbitrary rank. -/
theorem mixedRadialDiagonalCoefficient_sum (q : ℝ) (hq : q≠0) (n : ℕ) (p : OccupationPairLattice n) :
    (∑ i : Fin (n+1),mixedRadialDiagonalCoefficient q n i p)=
      q^(-(∑ i : Fin (n+1),p.1 i)-(∑ i : Fin (n+1),p.2 i)-(n:ℤ))*
        qInteger q ((∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2 i)+(n:ℤ)+1) := by
  let x : Fin (n+1) → ℤ := fun i =>p.1 i+p.2 i+1
  have hp : ∀ i : Fin (n+1),finiteIntegerPrefix (n+1) x i.castSucc=
      occupationStrictPrefix n i p.1+occupationStrictPrefix n i p.2+(i.val:ℤ) := by
    intro i
    change finiteIntegerPrefix (n+1) ((p.1+p.2)+(fun _ =>1)) i.castSucc=_
    rw [finiteIntegerPrefix_add,finiteIntegerPrefix_add,finiteIntegerPrefix_one]
    rfl
  have hs : (∑ i : Fin (n+1),x i)=(∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2 i)+(n:ℤ)+1 := by
    simp only [x,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    push_cast
    ring
  calc
    _ = ∑ i : Fin (n+1),q^(-2*finiteIntegerPrefix (n+1) x i.castSucc)*qGeometricInteger q (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp]
      unfold mixedRadialDiagonalCoefficient qGeometricInteger
      dsimp only [x]
      rw [← mul_assoc,← zpow_add₀ hq]
      congr 1
      congr 1
      ring
    _ = qGeometricInteger q (∑ i : Fin (n+1),x i) := qGeometricInteger_prefix_sum q hq (n+1) x
    _ = _ := by
      rw [hs]
      unfold qGeometricInteger
      congr 1
      congr 1
      ring

end AMSPhysical

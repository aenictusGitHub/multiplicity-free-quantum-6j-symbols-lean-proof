import QuantumOccupationEnergy
import QuantumMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def occupationFactorialProduct (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℝ :=
  ∏ k : Fin (n+1),qfactorial q ((x.val k).toNat)

theorem occupationFactorialProduct_pos (q : ℝ) (hq : 0<q) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) : 0<occupationFactorialProduct q n L x := by
  apply Finset.prod_pos
  intro k hk
  exact qfactorial_pos q hq _

theorem occupationFactorialProduct_raised (q : ℝ) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    qnum q ((x.val i.succ).toNat)*occupationFactorialProduct q n L (raisedOccupation n L x i hi)=
      qnum q ((x.val i.castSucc).toNat+1)*occupationFactorialProduct q n L x := by
  classical
  let y := raisedOccupation n L x i hi
  have he : ∀ k : Fin (n+1),
      (if k=i.succ then qnum q ((x.val i.succ).toNat) else 1)*qfactorial q ((y.val k).toNat)=
      (if k=i.castSucc then qnum q ((x.val i.castSucc).toNat+1) else 1)*qfactorial q ((x.val k).toNat) := by
    intro k
    by_cases hka : k=i.castSucc
    · subst k
      rw [if_neg (typeA_root_endpoints n i),if_pos rfl,one_mul]
      have hn : (y.val i.castSucc).toNat=(x.val i.castSucc).toNat+1 := by
        have ha := raisedOccupation_target n L x i hi
        have hx := x.property.1 i.castSucc
        dsimp [y]
        omega
      rw [hn,qfactorial_succ,mul_comm]
    · by_cases hkb : k=i.succ
      · subst k
        rw [if_pos rfl,if_neg hka,one_mul]
        have hn : (x.val i.succ).toNat=(y.val i.succ).toNat+1 := by
          have hb := raisedOccupation_source n L x i hi
          dsimp [y]
          omega
        rw [hn,qfactorial_succ,mul_comm]
      · rw [if_neg hkb,if_neg hka,one_mul,one_mul]
        rw [show y.val k=x.val k from raisedOccupation_other n L x i hi k hka hkb]
  have hp := Finset.prod_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun k _ => he k)
  simp only [Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true] at hp
  exact hp

end AMSPhysical
#print axioms AMSPhysical.occupationFactorialProduct_raised

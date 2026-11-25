import ActualAMSBoundary
import AMSDynkinPhaseMixedRoles

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem twoRowHighestWeight_as_singles (n : ℕ) (hn : 2≤n) (S r : ℕ) (hr : 2*r≤S) :
    twoRowHighestWeight n (by omega) S 0 r =
      Pi.single (⟨0,by omega⟩:Fin n) ((S-2*r:ℕ):ℤ)+Pi.single (⟨1,by omega⟩:Fin n) (r:ℤ) := by
  classical
  funext i
  have hC0 : i.castSucc=(0:Fin (n+1)) ↔ i=(⟨0,by omega⟩:Fin n) := by
    simp only [Fin.ext_iff,Fin.coe_castSucc,Fin.val_zero,Fin.val_mk]
  have hS0 : i.succ≠(0:Fin (n+1)) := by
    simp only [ne_eq,Fin.ext_iff,Fin.val_succ,Fin.val_zero];omega
  have hC1 : i.castSucc=secondVertex n (by omega) ↔ i=(⟨1,by omega⟩:Fin n) := by
    simp only [secondVertex,Fin.ext_iff,Fin.coe_castSucc,Fin.val_mk]
  have hS1 : i.succ=secondVertex n (by omega) ↔ i=(⟨0,by omega⟩:Fin n) := by
    simp only [secondVertex,Fin.ext_iff,Fin.val_succ,Fin.val_mk];omega
  have hC0' : (0:Fin (n+1))=i.castSucc ↔ (⟨0,by omega⟩:Fin n)=i := by
    rw [eq_comm,hC0,eq_comm]
  have hS0' : (0:Fin (n+1))≠i.succ := Ne.symm hS0
  have hC1' : secondVertex n (by omega)=i.castSucc ↔ (⟨1,by omega⟩:Fin n)=i := by
    rw [eq_comm,hC1,eq_comm]
  have hS1' : secondVertex n (by omega)=i.succ ↔ (⟨0,by omega⟩:Fin n)=i := by
    rw [eq_comm,hS1,eq_comm]
  simp only [twoRowHighestWeight,simpleOccupationWeight,twoRowOccupationWeight,Nat.add_zero,
    Pi.add_apply,Pi.single_apply]
  simp only [hC0,hS0,hC1,hS1,hC0',hS0',hC1',hS1',if_false]
  clear hC0 hS0 hC1 hS1 hC0' hS0' hC1' hS1'
  split_ifs <;> simp_all only [Fin.ext_iff,Fin.val_mk] <;> omega

theorem dynkinBox_twoRow (n : ℕ) (hn : 2≤n) (S r : ℕ) (hr : 2*r≤S) :
    dynkinBox n (twoRowHighestWeight n (by omega) S 0 r)=(S:ℤ) := by
  rw [twoRowHighestWeight_as_singles n hn S r hr,dynkinBox_add,dynkinBox_single,dynkinBox_single]
  simp only [Fin.val_mk,zero_add,Nat.cast_one,one_mul]
  omega

/-- At N=3 the two-row and mixed names coincide as actual Dynkin weights. -/
theorem twoRowHighestWeight_rank_three_mixed (S r : ℕ) (hr : 2*r≤S) :
    twoRowHighestWeight 2 (by omega) S 0 r=mixedHighestDynkin 2 (S-2*r) r := by
  rw [twoRowHighestWeight_as_singles 2 (by omega) S r hr,
    mixedHighestDynkin_as_singles 2 (by omega)]

theorem actualTwoRow_rank_three_alias (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (S r : ℕ) (hr : 2*r≤S) :
    (actualTwoRowCarrier q hq hq1 2 (by omega) S r hr).irrep =
      (actualMixedCarrier q hq hq1 2 (by omega) (S-2*r) r).irrep :=
  Subtype.ext (twoRowHighestWeight_rank_three_mixed S r hr)

theorem actualTwoRow_zero_symmetric_alias (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (S : ℕ) :
    (actualTwoRowCarrier q hq hq1 n (by omega) S 0 (by omega)).irrep =
      (actualSymmetricCarrier q hq hq1 n S).irrep := by
  apply Subtype.ext
  change twoRowHighestWeight n (by omega) S 0 0=mixedHighestDynkin n S 0
  rw [twoRowHighestWeight_as_singles n hn S 0 (by omega),
    mixedHighestDynkin_as_singles n (by omega)]
  simp

theorem amsDynkinVertexPhase_twoRow_outer (n : ℕ) (hn : 2≤n) (S r c d : ℕ)
    (hr : 2*r≤S) (hS : c+d=S) :
    amsDynkinVertexPhase n (twoRowHighestWeight n (by omega) S 0 r)
      (mixedHighestDynkin n 0 c) (mixedHighestDynkin n d 0)=(-1:ℝ)^((n-1)*c) := by
  apply amsDynkinVertexPhase_twoRow_sym_opp n hn
  rw [dynkinBox_twoRow n hn S r hr]
  exact_mod_cast hS.symm

end AMSPhysical
#print axioms AMSPhysical.actualTwoRow_rank_three_alias
#print axioms AMSPhysical.amsDynkinVertexPhase_twoRow_outer

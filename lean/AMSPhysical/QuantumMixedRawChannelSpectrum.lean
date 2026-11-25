import QuantumMixedContractionZero
import QuantumMixedRawAdjunction
import QuantumCupDiagonalDistinct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedCreationSpectralScalar_raw (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l m r : ℕ) (hrl : r≤l) :
    mixedCreationSpectralScalar q n l m r=mixedAnnihilationScale q n l m*
      quantumCupLeftEigenvalue q n (l+1) (m+1) 0 (r+1) := by
  have harg : ((l+m+n-r:ℕ):ℤ)=(l:ℤ)+(m:ℤ)+(n:ℤ)-(r:ℤ) := by omega
  unfold mixedCreationSpectralScalar mixedAnnihilationScale quantumCupLeftEigenvalue
  simp only [qnum_eq_qInteger q hq hq1,Nat.cast_add,Nat.cast_one,Nat.cast_zero]
  rw [harg]
  have hexp : -((l:ℤ)+1)-0-((m:ℤ)+1)-(n:ℤ)+2= -(l:ℤ)-(m:ℤ)-(n:ℤ) := by ring
  have hslot : (l:ℤ)+1+0+((m:ℤ)+1)+(n:ℤ)-((r:ℤ)+1)=(l:ℤ)+(m:ℤ)+(n:ℤ)-(r:ℤ)+1 := by ring
  rw [hexp,hslot]
  have hp : q^(-2*(l:ℤ)-2*(m:ℤ))=
      q^((n:ℤ)-(l:ℤ)-(m:ℤ))*q^(-(l:ℤ)-(m:ℤ)-(n:ℤ)) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  rw [hp]
  ring

theorem mixedFiniteRawRadial_channel_succ (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (hv : v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (l+1) (m+1) (mixedFusionIndexSucc l m r)) :
    mixedFiniteCreation q n l m (mixedFiniteRawAnnihilation q n l m v)=
      quantumCupLeftEigenvalue q n (l+1) (m+1) 0 (r.val+1) • v := by
  have hc:=mixedFiniteCreationContraction_channel q hq hq1 n hn l m r v hv
  rw [mixedFiniteContraction_eq_raw q hq hq1,map_smul,
    mixedCreationSpectralScalar_raw q hq hq1 n l m r.val (by have hr:=r.isLt;omega),← smul_smul] at hc
  exact smul_right_injective _ (ne_of_gt (mixedAnnihilationScale_pos q hq hq1 n l m)) hc

/-- The same closed channel eigenvalue applies to every actual irreducible
mixed tensor summand, including the zero-contraction summand. -/
theorem mixedFiniteRawRadial_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex (l+1) (m+1))
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (hv : v∈mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (l+1) (m+1) r) :
    mixedFiniteCreation q n l m (mixedFiniteRawAnnihilation q n l m v)=
      quantumCupLeftEigenvalue q n (l+1) (m+1) 0 r.val • v := by
  by_cases hr : r.val=0
  · have he : r=mixedFusionIndexZero (l+1) (m+1) := Fin.ext hr
    subst r
    have hc:=mixedFiniteContraction_zero_channel q hq hq1 n hn l m v hv
    rw [mixedFiniteContraction_eq_raw q hq hq1] at hc
    have hz : mixedFiniteRawAnnihilation q n l m v=0 :=
      (smul_eq_zero.mp hc).resolve_left (ne_of_gt (mixedAnnihilationScale_pos q hq hq1 n l m))
    rw [hz,map_zero]
    simp [quantumCupLeftEigenvalue,mixedFusionIndexZero]
  · let s : MixedFusionIndex l m:=⟨r.val-1,by have hh:=r.isLt;omega⟩
    have he : r=mixedFusionIndexSucc l m s := by
      apply Fin.ext
      change r.val=(r.val-1)+1
      omega
    rw [he] at hv ⊢
    exact mixedFiniteRawRadial_channel_succ q hq hq1 n hn l m s v hv

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteRawRadial_channel

import QuantumReverseRawSpectrum
import CompleteEigenchannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedFiniteRawRadial (q : ℝ) (n l m : ℕ) :
    Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :=
  (mixedFiniteCreation q n l m).comp (mixedFiniteRawAnnihilation q n l m)

def reverseMixedRawRadial (q : ℝ) (n l m : ℕ) :
    Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :=
  (reverseMixedFiniteCreation q n l m).comp (reverseMixedRawAnnihilation q n l m)

theorem mixedRawRadialEigenvalue_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    Function.Injective (fun r : MixedFusionIndex l m =>quantumCupLeftEigenvalue q n l m 0 r.val) := by
  intro r s he
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hh|hh
  · have hs:=quantumCupLeftEigenvalue_strict q hq hq1 n hn l m 0 s.val r.val hh
      (by have hs:=s.isLt;omega) (by have hs:=s.isLt;omega)
    exact (ne_of_lt hs) he
  · have hs:=quantumCupLeftEigenvalue_strict q hq hq1 n hn l m 0 r.val s.val hh
      (by have hr:=r.isLt;omega) (by have hr:=r.isLt;omega)
    exact (ne_of_gt hs) he

/-- The physical channel identification is proved as an equality of actual
submodules, so no eigenvector-to-irrep identification is assumed. -/
theorem mixedFiniteRawRadial_eigenspace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex (l+1) (m+1)) :
    Module.End.eigenspace (R:=ℝ)
      (M:=quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
      (mixedFiniteRawRadial q n l m) (quantumCupLeftEigenvalue q n (l+1) (m+1) 0 r.val)=
      mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact completeEigenchannel_eq (V:=V)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1))
    (mixedFusionEquiv q hq hq1 n hn (l+1) (m+1)).bijective (mixedFiniteRawRadial q n l m) _
    (mixedRawRadialEigenvalue_injective q hq hq1 n hn (l+1) (m+1))
    (mixedFiniteRawRadial_channel q hq hq1 n hn l m) r

theorem reverseMixedRawRadial_eigenspace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex (l+1) (m+1)) :
    Module.End.eigenspace (R:=ℝ)
      (M:=quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
      (reverseMixedRawRadial q n l m) (quantumCupLeftEigenvalue q n (l+1) (m+1) 0 r.val)=
      reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let S := reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1)
  have hOrth : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,reverseMixedTensorBilin q n (l+1) (m+1) x y=0 := by
    intro i j hij x hx y hy
    exact reverseMixedFusionChannels_orthogonal q hq hq1 n hn (l+1) (m+1) i j hij x y hx hy
  exact completeEigenchannel_eq (V:=V) S
    ⟨submoduleFamilySum_injective (reverseMixedTensorBilin q n (l+1) (m+1))
      (reverseMixedTensorBilin_definite q hq n (l+1) (m+1)) S hOrth,
      submoduleFamilySum_surjective S (reverseMixedFusionSpan_eq_top q hq hq1 n hn (l+1) (m+1))⟩
    (reverseMixedRawRadial q n l m) _ (mixedRawRadialEigenvalue_injective q hq hq1 n hn (l+1) (m+1))
    (reverseMixedRawRadial_channel q hq hq1 n hn l m) r

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteRawRadial_eigenspace
#print axioms AMSPhysical.reverseMixedRawRadial_eigenspace

import RankTwoTypeIIRightChannel
import QuantumMixedInputSpectrum

set_option autoImplicit false
noncomputable section
namespace AMSPhysical

theorem typeIIRightIndex_injective (a b c:ℕ):Function.Injective (typeIIRightIndex a b c) := by
  intro s t he
  have hv:=congrArg Fin.val he
  rw [typeIIRightIndex_val,typeIIRightIndex_val] at hv
  have hs:=s.val.isLt
  have ht:=t.val.isLt
  apply Subtype.ext
  apply Fin.ext
  omega

theorem typeIIRightCreationSpectrum_injective (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n) (a b c:ℕ):
    Function.Injective (fun t:QuantumCupIndex a c b=>mixedCreationSpectralScalar q n b c (c-t.val.val)) := by
  simpa only [typeIIRightIndex_val] using
    (mixedCreationSpectralScalar_injective q hq hq1 n hn b c).comp (typeIIRightIndex_injective a b c)

end AMSPhysical
#print axioms AMSPhysical.typeIIRightCreationSpectrum_injective

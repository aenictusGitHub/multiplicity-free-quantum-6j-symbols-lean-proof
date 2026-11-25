import AMSClassicalLimit

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Filter
open scoped Topology

/-- The actual physical classical-limit coefficient, defined as the limit
of the independently constructed physical deformed coefficient. -/
def physicalTypeIIClassicalLimit (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):ℝ:=
  limUnder (𝓝[≠] (1:ℝ)) (physicalTypeIIWignerFunction h a b c d hbal r t)

theorem physicalTypeII_classical_AMS (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    physicalTypeIIClassicalLimit h a b c d hbal r t=
      ordinaryFourTrianglePrefactor h (a:ℤ) b c d (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) :=
  (physicalTypeII_AMS_q_one_limit h a b c d hbal r t).limUnder_eq

def physicalTypeIClassicalLimit (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c):ℝ:=
  limUnder (𝓝[≠] (1:ℝ)) (physicalTypeIWignerFunction h l m c hadm s t)

theorem physicalTypeI_classical_AMS (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c):
    physicalTypeIClassicalLimit h l m c hadm s t=
      ordinaryFourTrianglePrefactor h (l:ℤ) m c (l+c-m) (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
        AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h false (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) :=
  (physicalTypeI_AMS_q_one_limit h l m c hadm s t).limUnder_eq

end AMSPhysical
#print axioms AMSPhysical.physicalTypeII_classical_AMS
#print axioms AMSPhysical.physicalTypeI_classical_AMS

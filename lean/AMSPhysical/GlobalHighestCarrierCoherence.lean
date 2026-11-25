import CompactHighestChannelTransfer
import CyclicIntertwinerUnique

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W Z : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

theorem CompactHighestRealization.transport_unique (hq : q ≠ 0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (f : X.channel →ₗ[ℝ] W)
    (hf : ∀ z x, f (X.channelAction z x) = Y.action z (f x))
    (hh : f ⟨X.highest, algebraCyclicSpan_self _ _⟩ = Y.highest) :
    f = Y.channel.subtype.comp (X.transport hq Y).toLinearMap := by
  apply cyclic_intertwiner_unique X.action Y.action X.highest f _ hf
  · intro z x
    exact (X.transport_intertwines hq Y z x)
  · exact hh.trans (X.transport_highest hq Y).symm

/-- Canonical normalized highest carriers have exactly coherent transport,
with no residual sign depending on an intermediate tensor realization. -/
theorem CompactHighestRealization.transport_comp (hq : q ≠ 0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (T : CompactHighestRealization q n Z lam) (x : X.channel) :
    Y.transport hq T (X.transport hq Y x) = X.transport hq T x := by
  let f : X.channel →ₗ[ℝ] Z :=
    T.channel.subtype.comp ((Y.transport hq T).toLinearMap.comp (X.transport hq Y).toLinearMap)
  have hf : ∀ z x, f (X.channelAction z x) = T.action z (f x) := by
    intro z v
    have he : X.transport hq Y (X.channelAction z v) = Y.channelAction z (X.transport hq Y v) := by
      apply Subtype.ext
      exact X.transport_intertwines hq Y z v
    change (Y.transport hq T (X.transport hq Y (X.channelAction z v))).val = _
    rw [he]
    exact Y.transport_intertwines hq T z (X.transport hq Y v)
  have hh : f ⟨X.highest, algebraCyclicSpan_self _ _⟩ = T.highest := by
    have he : X.transport hq Y ⟨X.highest, algebraCyclicSpan_self _ _⟩ =
        ⟨Y.highest, algebraCyclicSpan_self _ _⟩ := Subtype.ext (X.transport_highest hq Y)
    change (Y.transport hq T (X.transport hq Y ⟨X.highest, algebraCyclicSpan_self _ _⟩)).val = _
    rw [he]
    exact Y.transport_highest hq T
  apply Subtype.ext
  exact DFunLike.congr_fun (X.transport_unique hq T f hf hh) x

theorem CompactHighestRealization.transport_self (hq : q ≠ 0)
    (X : CompactHighestRealization q n V lam) (x : X.channel) :
    X.transport hq X x = x := by
  have he := X.transport_unique hq X X.channel.subtype (fun _ _ => rfl) rfl
  apply Subtype.ext
  exact (DFunLike.congr_fun he x).symm

/-- Full pair transfer through any fixed highest carrier composes exactly.
This applies to the actual mixed and two-row Clebsch constructions in all ranks. -/
theorem CompactHighestRealization.channelTransfer_comp
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] (hq : q ≠ 0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (T : CompactHighestRealization q n Z lam) :
    (Y.channelTransfer hq T).comp (X.channelTransfer hq Y) = X.channelTransfer hq T := by
  apply LinearMap.ext
  intro v
  change (Y.transport hq T (Y.channelProjection (X.transport hq Y (X.channelProjection v)).val)).val =
    (X.transport hq T (X.channelProjection v)).val
  rw [Y.channelProjection_subtype, X.transport_comp hq Y T]

/-- A pair map factors through a carrier chosen only from the internal
highest weight. The carrier is independent of the two exterior pairs. -/
theorem CompactHighestRealization.channelTransfer_factor
    [FiniteDimensional ℝ V] (hq : q ≠ 0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (T : CompactHighestRealization q n Z lam) :
    X.channelTransfer hq Y =
      (Y.channel.subtype.comp (T.transport hq Y).toLinearMap).comp
        ((X.transport hq T).toLinearMap.comp X.channelProjection) := by
  apply LinearMap.ext
  intro v
  change (X.transport hq Y (X.channelProjection v)).val =
    (T.transport hq Y (X.transport hq T (X.channelProjection v))).val
  rw [X.transport_comp hq T Y]

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.transport_comp
#print axioms AMSPhysical.CompactHighestRealization.channelTransfer_comp

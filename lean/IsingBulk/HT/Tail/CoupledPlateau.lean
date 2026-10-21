import IsingBulk.HT.Tail.CoupledOccupancy
import IsingBulk.Tail.MixedActiveRestriction

/-!
# Exact coupled occupancy on the true branch plateau

The spectator occupancy is not discarded. Its restricted constancy follows
from the actual selector plateau germ. This proves all restricted angular
jets vanish and that the full Jacobian acts by `i` on plateau-supported
fields. These are the algebraic cancellations used by the onsite one-phase
regularization; its uniform integral estimate is a separate obligation.
-/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail Filter
open scoped Topology BigOperators

/-- Vanishing is imposed only where the field is supported. The other
coordinates may have nonzero selector derivatives and nonzero occupancy. -/
theorem coupled_angular_action_of_plateau_support {N : ℕ}
    (lam tau : ℝ) (p m p' m' : Fin N → ℝ) (V : Fin N → ℂ)
    (hV : ∀ j, V j ≠ 0 → p' j = 0 ∧ m' j = 0) (i : Fin N) :
    (∑ j, retractionJacobian lam tau p m p' m' i j * V j) =
      Complex.I * V i := by
  calc
    _ = ∑ j, (if i = j then Complex.I else 0) * V j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : V j = 0
      · simp only [hj, mul_zero]
      · rw [retractionJacobian_named_column lam tau p m p' m' j
          (hV j hj).1 (hV j hj).2 i]
    _ = _ := by simp

/-- The genuine lower core supplies the plateau germs, rather than an
independently frozen occupancy parameter. -/
theorem constructed_core_plateau_germs {N : ℕ} (S : Finset (Fin N))
    (theta : Fin N → ℝ) {b eta alpha : ℝ}
    (hb : 0 < Real.sin b) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.sin b / 4) (halpha : 0 < alpha)
    (hcore : ∀ i ∈ S, lowerChord b (theta i) < eta ^ 2) :
    (∀ i ∈ S, (constructedSelector b eta alpha).p =ᶠ[𝓝 (theta i)]
      fun _ => (constructedSelector b eta alpha).p (theta i)) ∧
    (∀ i ∈ S, (constructedSelector b eta alpha).m =ᶠ[𝓝 (theta i)]
      fun _ => (constructedSelector b eta alpha).m (theta i)) := by
  constructor
  · intro i hi
    have h := (constructed_branch_plateau_germ hb heta hetaSmall halpha (hcore i hi)).1
    exact h.trans (Eventually.of_forall (fun _ => h.eq_of_nhds.symm))
  · intro i hi
    have h := (constructed_branch_plateau_germ hb heta hetaSmall halpha (hcore i hi)).2
    exact h.trans (Eventually.of_forall (fun _ => h.eq_of_nhds.symm))

/-- Actual branch-supported fields have the claimed full matrix action.
The derivative zeros are derived from strict selector-core membership. -/
theorem constructed_coupled_branch_action {N : ℕ} (S : Finset (Fin N))
    (theta : Fin N → ℝ) {b eta alpha : ℝ} (tau lam : ℝ)
    (hb : 0 < Real.sin b) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.sin b / 4) (halpha : 0 < alpha)
    (hcore : ∀ i ∈ S, lowerChord b (theta i) < eta ^ 2)
    (V : Fin N → ℂ) (hV : ∀ i, i ∉ S → V i = 0) (i : Fin N) :
    (∑ j, angularJacobian (constructedSelector b eta alpha) tau lam theta i j * V j) =
      Complex.I * V i := by
  apply coupled_angular_action_of_plateau_support
  intro j hj
  have hjs : j ∈ S := by
    by_contra hnot
    exact hj (hV j hnot)
  have h := constructed_branch_plateau_germ hb heta hetaSmall halpha (hcore j hjs)
  exact ⟨by simpa only [deriv_const] using h.1.deriv_eq,
    by simpa only [deriv_const] using h.2.deriv_eq⟩

/-- Restricted occupancy is locally constant only after restricting to
actual plateau-supported coordinates; spectator values remain unchanged. -/
theorem coupled_occupancy_plateau_germ {N : ℕ} (S : Finset (Fin N))
    (theta : Fin N → ℝ) {b eta alpha : ℝ}
    (hb : 0 < Real.sin b) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.sin b / 4) (halpha : 0 < alpha)
    (hcore : ∀ i ∈ S, lowerChord b (theta i) < eta ^ 2) :
    (fun x : Fin N → ℝ => normalizedAngularOccupancy N
      (constructedSelector b eta alpha).p (mixedFreeze S theta x)) =ᶠ[𝓝 theta]
      fun _ => normalizedAngularOccupancy N (constructedSelector b eta alpha).p theta := by
  have hp := (constructed_core_plateau_germs S theta hb heta hetaSmall halpha hcore).1
  filter_upwards [mixed_plateau_data_eventually S theta
    (constructedSelector b eta alpha).p hp] with x hx
  have hdata := mixedFreeze_data S theta x (constructedSelector b eta alpha).p
    (fun i hi => (hx i hi).1)
  unfold normalizedAngularOccupancy
  rw [hdata]

/-- Every positive-order restricted jet is zero. This is an all-order
germ consequence, not a first-derivative occupancy simplification. -/
theorem coupled_occupancy_plateau_jets {N : ℕ} (S : Finset (Fin N))
    (theta : Fin N → ℝ) {b eta alpha : ℝ}
    (hb : 0 < Real.sin b) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.sin b / 4) (halpha : 0 < alpha)
    (hcore : ∀ i ∈ S, lowerChord b (theta i) < eta ^ 2)
    (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (fun x : Fin N → ℝ => normalizedAngularOccupancy N
      (constructedSelector b eta alpha).p (mixedFreeze S theta x)) theta = 0 := by
  have hg := coupled_occupancy_plateau_germ S theta hb heta hetaSmall halpha hcore
  have h := (hg.iteratedFDeriv ℝ k).eq_of_nhds
  simpa only [iteratedFDeriv_const_of_ne hk, Pi.zero_apply] using h

/-- The whole coupled matrix and every spectator contour point have the
proved plateau germ. The occupancy and its cross-coordinate terms remain
present in both sides of the identity. -/
theorem coupled_branch_contour_germ {N : ℕ} (S : Finset (Fin N))
    (theta : Fin N → ℝ) {b eta alpha : ℝ} (r tau lam : ℝ)
    (hb : 0 < Real.sin b) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.sin b / 4) (halpha : 0 < alpha)
    (hcore : ∀ i ∈ S, lowerChord b (theta i) < eta ^ 2) :
    ∀ᶠ x in 𝓝 theta,
      angularJacobian (constructedSelector b eta alpha) tau lam (mixedFreeze S theta x) =
        angularJacobian (constructedSelector b eta alpha) tau lam theta ∧
      ∀ i, deformedPoint (constructedSelector b eta alpha) r tau lam
          (mixedFreeze S theta x) i =
        deformedPoint (constructedSelector b eta alpha) r tau lam theta i *
          Complex.exp (Complex.I * ((mixedFreeze S theta x i : ℂ) - (theta i : ℂ))) := by
  obtain ⟨hp, hm⟩ := constructed_core_plateau_germs S theta hb heta hetaSmall halpha hcore
  exact mixed_active_contour_germ S theta (constructedSelector b eta alpha) r tau lam hp hm

end
end IsingBulk.HT.Tail

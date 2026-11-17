import IsingBulk.AnisoF002.C03.IsotropicAwaySupportBound
import IsingBulk.AnisoF002.C03.RegularCollisionIntegral
import IsingBulk.AnisoF002.C03.RegularAngularSplit

/-!
# The actual smooth split at total coincidence

The centered quadratic is exactly the frozen zero-sum quadratic on each
original mean chart. The near weight is one on Q≤r and supported on
Q≤2r; the complementary weight has a genuine positive-diameter support.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators ContDiff

def angularCenteredQuadratic {N : ℕ} (θ : Fin N → ℝ) : ℝ :=
  ∑ i, (θ i - angularMean θ) ^ 2

theorem angularMean_contDiff (N : ℕ) : ContDiff ℝ ∞ (angularMean : (Fin N → ℝ) → ℝ) := by
  unfold angularMean
  exact (ContDiff.sum (fun i _ => contDiff_apply ℝ ℝ i)).div_const _

theorem angularCenteredQuadratic_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (angularCenteredQuadratic : (Fin N → ℝ) → ℝ) :=
  ContDiff.sum (fun i _ => ((contDiff_apply ℝ ℝ i).sub (angularMean_contDiff N)).pow 2)

theorem angularMean_centeredConstraintAngles {n : ℕ} (μ : ℝ) (x : Fin n → ℝ) :
    angularMean (centeredConstraintAngles μ x) = μ := by
  rw [angularMean, centeredConstraintAngles_sum]
  push_cast
  field_simp

theorem angularCenteredQuadratic_centered {n : ℕ} (μ : ℝ) (x : Fin n → ℝ) :
    angularCenteredQuadratic (centeredConstraintAngles μ x) = angularQuadratic (flatConstrainedAngles x) := by
  unfold angularCenteredQuadratic
  rw [angularMean_centeredConstraintAngles]
  have he : (fun i => centeredConstraintAngles μ x i - μ) = flatConstrainedAngles x := by
    rw [centeredConstraintAngles_sub_const, constrainedTangentMap_apply]
    rfl
  change angularQuadratic (fun i => centeredConstraintAngles μ x i - μ) = _
  rw [he]

theorem angularCenteredQuadratic_const {N : ℕ} (hN : 0 < N) (c : ℝ) :
    angularCenteredQuadratic (fun _ : Fin N => c) = 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : angularMean (fun _ : Fin N => c) = c := by
    simp only [angularMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp only [angularCenteredQuadratic, hm, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero]

theorem angularCenteredQuadratic_pos_nonconstant {N : ℕ} (hN : 0 < N) (θ : Fin N → ℝ)
    (hq : 0 < angularCenteredQuadratic θ) : ∃ i l, θ i ≠ θ l := by
  by_contra hh
  push Not at hh
  let i₀ : Fin N := ⟨0, hN⟩
  have he : θ = fun _ => θ i₀ := funext (fun i => hh i i₀)
  rw [he, angularCenteredQuadratic_const hN] at hq
  exact lt_irrefl _ hq

def collisionAwayCutoff {N : ℕ} (r : ℝ) (θ : Fin N → ℝ) : ℝ :=
  Real.smoothTransition ((angularCenteredQuadratic θ - r) / r)

def collisionNearCutoff {N : ℕ} (r : ℝ) (θ : Fin N → ℝ) : ℝ :=
  1 - collisionAwayCutoff r θ

def weightedCollisionAway {N : ℕ} (r : ℝ) (g : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ) : ℂ :=
  g θ * (collisionAwayCutoff r θ : ℂ)

def weightedCollisionNear {N : ℕ} (r : ℝ) (g : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ) : ℂ :=
  g θ * (collisionNearCutoff r θ : ℂ)

theorem collisionAwayCutoff_contDiff (N : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (collisionAwayCutoff (N := N) r) :=
  Real.smoothTransition.contDiff.comp (((angularCenteredQuadratic_contDiff N).sub contDiff_const).div_const r)

theorem collisionNearCutoff_contDiff (N : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (collisionNearCutoff (N := N) r) :=
  contDiff_const.sub (collisionAwayCutoff_contDiff N r)

theorem weightedCollisionAway_contDiff {N : ℕ} (r : ℝ) {g : (Fin N → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (weightedCollisionAway r g) :=
  hg.mul (Complex.ofRealCLM.contDiff.comp (collisionAwayCutoff_contDiff N r))

theorem weightedCollisionNear_contDiff {N : ℕ} (r : ℝ) {g : (Fin N → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (weightedCollisionNear r g) :=
  hg.mul (Complex.ofRealCLM.contDiff.comp (collisionNearCutoff_contDiff N r))

theorem collisionCutoff_bounds {N : ℕ} (r : ℝ) (θ : Fin N → ℝ) :
    collisionAwayCutoff r θ ∈ Icc 0 1 ∧ collisionNearCutoff r θ ∈ Icc 0 1 := by
  have h₀ := Real.smoothTransition.nonneg ((angularCenteredQuadratic θ - r) / r)
  have h₁ := Real.smoothTransition.le_one ((angularCenteredQuadratic θ - r) / r)
  exact ⟨⟨h₀, h₁⟩, ⟨by dsimp [collisionNearCutoff, collisionAwayCutoff]; linarith,
    by dsimp [collisionNearCutoff, collisionAwayCutoff]; linarith⟩⟩

theorem collisionAwayCutoff_zero {N : ℕ} {r : ℝ} (hr : 0 < r) (θ : Fin N → ℝ)
    (hθ : angularCenteredQuadratic θ ≤ r) : collisionAwayCutoff r θ = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ) hr.le)

theorem collisionNearCutoff_one {N : ℕ} {r : ℝ} (hr : 0 < r) (θ : Fin N → ℝ)
    (hθ : angularCenteredQuadratic θ ≤ r) : collisionNearCutoff r θ = 1 := by
  rw [collisionNearCutoff, collisionAwayCutoff_zero hr θ hθ, sub_zero]

theorem collisionNearCutoff_zero {N : ℕ} {r : ℝ} (hr : 0 < r) (θ : Fin N → ℝ)
    (hθ : 2 * r ≤ angularCenteredQuadratic θ) : collisionNearCutoff r θ = 0 := by
  have ha : collisionAwayCutoff r θ = 1 := Real.smoothTransition.one_of_one_le
    ((one_le_div hr).mpr (by linarith))
  rw [collisionNearCutoff, ha, sub_self]

theorem weightedCollisionAway_tsupport {N : ℕ} {r : ℝ} (hr : 0 < r)
    (g : (Fin N → ℝ) → ℂ) {θ : Fin N → ℝ} (hθ : θ ∈ tsupport (weightedCollisionAway r g)) :
    θ ∈ tsupport g ∧ r ≤ angularCenteredQuadratic θ := by
  refine ⟨tsupport_mul_subset_left hθ, ?_⟩
  have hsub : tsupport (weightedCollisionAway r g) ⊆ {y | r ≤ angularCenteredQuadratic y} := by
    apply closure_minimal _ (isClosed_le continuous_const (angularCenteredQuadratic_contDiff N).continuous)
    intro y hy
    by_contra hh
    have hz := collisionAwayCutoff_zero hr y (le_of_lt (lt_of_not_ge hh))
    exact hy (by simp only [weightedCollisionAway, hz, Complex.ofReal_zero, mul_zero])
  exact hsub hθ

theorem weightedCollisionNear_tsupport {N : ℕ} {r : ℝ} (hr : 0 < r)
    (g : (Fin N → ℝ) → ℂ) {θ : Fin N → ℝ} (hθ : θ ∈ tsupport (weightedCollisionNear r g)) :
    θ ∈ tsupport g ∧ angularCenteredQuadratic θ ≤ 2 * r := by
  refine ⟨tsupport_mul_subset_left hθ, ?_⟩
  have hsub : tsupport (weightedCollisionNear r g) ⊆ {y | angularCenteredQuadratic y ≤ 2 * r} := by
    apply closure_minimal _ (isClosed_le (angularCenteredQuadratic_contDiff N).continuous continuous_const)
    intro y hy
    by_contra hh
    have hz := collisionNearCutoff_zero hr y (le_of_lt (lt_of_not_ge hh))
    exact hy (by simp only [weightedCollisionNear, hz, Complex.ofReal_zero, mul_zero])
  exact hsub hθ

theorem weightedCollisionAway_nonconstant {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (g : (Fin N → ℝ) → ℂ) {θ : Fin N → ℝ} (hθ : θ ∈ tsupport (weightedCollisionAway r g)) :
    ∃ i l, θ i ≠ θ l :=
  angularCenteredQuadratic_pos_nonconstant hN θ (hr.trans_le (weightedCollisionAway_tsupport hr g hθ).2)

theorem weightedCollision_exact_split {N : ℕ} (r : ℝ) (g : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ) :
    g θ = weightedCollisionNear r g θ + weightedCollisionAway r g θ := by
  unfold weightedCollisionNear weightedCollisionAway collisionNearCutoff
  push_cast
  ring

end
end IsingBulk.AnisoF002.Isotropic

import IsingBulk.AnisoF002.C03.IsotropicPeriodicBumpJets

/-!
# An actual smooth periodic cutoff for the isotropic right part

The right plateau endpoint is independent of the small branch buffer.
Its return can therefore be placed in the excluded upper population
plateau.  No complex extension of this real smooth function is used.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

def rightCutoffCenter (b δ ρ : ℝ) : ℝ := (ρ - b - δ / 2) / 2
def rightCutoffInnerRadius (b δ ρ : ℝ) : ℝ := (ρ + b + δ / 2) / 2
def rightCutoffOuterRadius (b δ ρ : ℝ) : ℝ := rightCutoffInnerRadius b δ ρ + δ / 2

def periodicRightCutoff (b δ ρ θ : ℝ) : ℝ :=
  Real.smoothTransition
    ((Real.cos (θ - rightCutoffCenter b δ ρ) - Real.cos (rightCutoffOuterRadius b δ ρ)) /
      (Real.cos (rightCutoffInnerRadius b δ ρ) - Real.cos (rightCutoffOuterRadius b δ ρ)))

structure RightCutoffGeometry (b δ ρ : ℝ) : Prop where
  b_pos : 0 < b
  delta_pos : 0 < δ
  rho_pos : 0 < ρ
  left_gap : b + δ < Real.pi
  right_gap : ρ + δ / 2 < Real.pi

theorem rightCutoff_endpoints (b δ ρ : ℝ) :
    rightCutoffCenter b δ ρ - rightCutoffInnerRadius b δ ρ = -b - δ / 2 ∧
    rightCutoffCenter b δ ρ + rightCutoffInnerRadius b δ ρ = ρ ∧
    rightCutoffCenter b δ ρ - rightCutoffOuterRadius b δ ρ = -b - δ ∧
    rightCutoffCenter b δ ρ + rightCutoffOuterRadius b δ ρ = ρ + δ / 2 := by
  dsimp [rightCutoffCenter, rightCutoffInnerRadius, rightCutoffOuterRadius]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem RightCutoffGeometry.radii {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) :
    0 < rightCutoffInnerRadius b δ ρ ∧
    rightCutoffInnerRadius b δ ρ < rightCutoffOuterRadius b δ ρ ∧
    rightCutoffOuterRadius b δ ρ < Real.pi := by
  have hb := h.b_pos
  have hd := h.delta_pos
  have hr := h.rho_pos
  have hl := h.left_gap
  have hu := h.right_gap
  dsimp [rightCutoffInnerRadius, rightCutoffOuterRadius]
  constructor
  · positivity
  constructor <;> linarith

theorem RightCutoffGeometry.cos_gap {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) :
    0 < Real.cos (rightCutoffInnerRadius b δ ρ) - Real.cos (rightCutoffOuterRadius b δ ρ) := by
  have hr := h.radii
  exact sub_pos.mpr (Real.cos_lt_cos_of_nonneg_of_le_pi hr.1.le hr.2.2.le hr.2.1)

theorem periodicRightCutoff_bounds (b δ ρ θ : ℝ) :
    0 ≤ periodicRightCutoff b δ ρ θ ∧ periodicRightCutoff b δ ρ θ ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem periodicRightCutoff_contDiff (b δ ρ : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (periodicRightCutoff b δ ρ) :=
  Real.smoothTransition.contDiff.comp
    (((Real.contDiff_cos.comp (contDiff_id.sub contDiff_const)).sub contDiff_const).div_const _)

theorem periodicRightCutoff_periodic (b δ ρ : ℝ) :
    Function.Periodic (periodicRightCutoff b δ ρ) (2 * Real.pi) := by
  intro θ
  unfold periodicRightCutoff
  rw [show θ + 2 * Real.pi - rightCutoffCenter b δ ρ =
    (θ - rightCutoffCenter b δ ρ) + 2 * Real.pi by ring, Real.cos_add_two_pi]

theorem periodicRightCutoff_one {b δ ρ θ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hθ : θ ∈ Icc (-b - δ / 2) ρ) : periodicRightCutoff b δ ρ θ = 1 := by
  have he := rightCutoff_endpoints b δ ρ
  have habs : |θ - rightCutoffCenter b δ ρ| ≤ rightCutoffInnerRadius b δ ρ := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2, he.1, he.2.1]
  have hcos : Real.cos (rightCutoffInnerRadius b δ ρ) ≤
      Real.cos (θ - rightCutoffCenter b δ ρ) := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg (θ - rightCutoffCenter b δ ρ))
      (h.radii.2.1.le.trans h.radii.2.2.le) habs
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div h.cos_gap).mpr
  linarith

theorem cos_le_cos_of_outside_arc {t R : ℝ} (hR : 0 ≤ R)
    (hlo : R ≤ |t|) (hhi : |t| ≤ 2 * Real.pi - R) : Real.cos t ≤ Real.cos R := by
  rw [← Real.cos_abs t]
  by_cases ht : |t| ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hR ht hlo
  · calc
      _ = Real.cos (2 * Real.pi - |t|) := (Real.cos_two_pi_sub |t|).symm
      _ ≤ _ := Real.cos_le_cos_of_nonneg_of_le_pi hR (by linarith) (by linarith)

theorem periodicRightCutoff_zero {b δ ρ θ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hθ : θ ∈ Icc (-Real.pi) Real.pi)
    (hout : θ ≤ -b - δ ∨ ρ + δ / 2 ≤ θ) : periodicRightCutoff b δ ρ θ = 0 := by
  have he := rightCutoff_endpoints b δ ρ
  have hL : -Real.pi < rightCutoffCenter b δ ρ - rightCutoffOuterRadius b δ ρ := by
    rw [he.2.2.1]
    linarith [h.left_gap]
  have hR : rightCutoffCenter b δ ρ + rightCutoffOuterRadius b δ ρ < Real.pi := by
    rw [he.2.2.2]
    exact h.right_gap
  have hlo : rightCutoffOuterRadius b δ ρ ≤ |θ - rightCutoffCenter b δ ρ| := by
    rcases hout with hl | hr
    · linarith [neg_le_abs (θ - rightCutoffCenter b δ ρ), he.2.2.1]
    · linarith [le_abs_self (θ - rightCutoffCenter b δ ρ), he.2.2.2]
  have hhi : |θ - rightCutoffCenter b δ ρ| ≤ 2 * Real.pi - rightCutoffOuterRadius b δ ρ := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have hcos := cos_le_cos_of_outside_arc (h.radii.1.le.trans h.radii.2.1.le) hlo hhi
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcos) h.cos_gap.le

theorem periodicRightCutoff_support {b δ ρ θ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) (hne : periodicRightCutoff b δ ρ θ ≠ 0) :
    θ ∈ Ioo (-b - δ) (ρ + δ / 2) := by
  constructor
  · by_contra hh
    exact hne (periodicRightCutoff_zero h hθ (Or.inl (le_of_not_gt hh)))
  · by_contra hh
    exact hne (periodicRightCutoff_zero h hθ (Or.inr (le_of_not_gt hh)))

theorem periodicRightCutoff_scalar_jets (b δ ρ : ℝ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ FiniteJetControl k (periodicRightCutoff b δ ρ) C :=
  periodic_finiteJetControl _ (2 * Real.pi) (by positivity)
    (periodicRightCutoff_periodic b δ ρ) (fun _ => periodicRightCutoff_contDiff b δ ρ) k

end
end IsingBulk.AnisoF002.Isotropic

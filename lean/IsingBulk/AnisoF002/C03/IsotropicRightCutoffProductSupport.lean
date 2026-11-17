import IsingBulk.AnisoF002.C03.IsotropicRightCutoffProducts

/-!
# Every actual right-product jet lies in the fixed right rectangle

The support proof is global and periodic before a fundamental interval
is chosen. It therefore applies equally to the original angular box and
the shifted box used by compact left anchors, with explicit endpoint gaps.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open Set Filter
open scoped Topology BigOperators Classical

theorem cos_lt_cos_of_outside_arc {t R : ℝ} (hR : 0 ≤ R)
    (hlo : R < |t|) (hhi : |t| < 2 * Real.pi - R) : Real.cos t < Real.cos R := by
  rw [← Real.cos_abs t]
  by_cases ht : |t| ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hR ht hlo
  · calc
      _ = Real.cos (2 * Real.pi - |t|) := (Real.cos_two_pi_sub |t|).symm
      _ < _ := Real.cos_lt_cos_of_nonneg_of_le_pi hR (by linarith) (by linarith)

theorem rightCutoffProduct_weighted_tsupport_cos {b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) {N : ℕ} (w : (Fin N → ℝ) → ℂ) (i : Fin N) :
    tsupport (fun θ => w θ * rightCutoffProduct b δ ρ N θ) ⊆
      {θ : Fin N → ℝ | Real.cos (rightCutoffOuterRadius b δ ρ) ≤
        Real.cos (θ i - rightCutoffCenter b δ ρ)} := by
  apply closure_minimal
  · intro θ hθ
    have hp : rightCutoffProduct b δ ρ N θ ≠ 0 := (mul_ne_zero_iff.mp hθ).2
    have hi : periodicRightCutoff b δ ρ (θ i) ≠ 0 := by
      intro hz
      apply hp
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hz, Complex.ofReal_zero]
    by_contra hc
    apply hi
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hc)) h.cos_gap.le
  · exact isClosed_le continuous_const (Real.continuous_cos.comp ((continuous_apply i).sub continuous_const))

theorem rightCutoffProduct_weighted_jet_rectangle {b δ ρ L : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hL : L < -b - δ)
    (hU : ρ + δ / 2 < L + 2 * Real.pi) {N : ℕ}
    (w : (Fin N → ℝ) → ℂ) (k : ℕ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i ∈ Icc L (L + 2 * Real.pi))
    (hne : iteratedFDeriv ℝ k (fun x => w x * rightCutoffProduct b δ ρ N x) θ ≠ 0) :
    ∀ i, θ i ∈ Icc (-b - δ) (ρ + δ / 2) := by
  intro i
  have hc := rightCutoffProduct_weighted_tsupport_cos h w i ((support_iteratedFDeriv_subset k) hne)
  have he := rightCutoff_endpoints b δ ρ
  have hR : 0 ≤ rightCutoffOuterRadius b δ ρ := h.radii.1.le.trans h.radii.2.1.le
  have hhi : |θ i - rightCutoffCenter b δ ρ| < 2 * Real.pi - rightCutoffOuterRadius b δ ρ := by
    rw [abs_lt]
    constructor <;> linarith only [(hθ i).1, (hθ i).2, hL, hU, he.2.2.1, he.2.2.2]
  constructor
  · by_contra hl
    have hlo : rightCutoffOuterRadius b δ ρ < |θ i - rightCutoffCenter b δ ρ| := by
      have hh := neg_le_abs (θ i - rightCutoffCenter b δ ρ)
      linarith only [hl, hh, he.2.2.1]
    exact (not_lt_of_ge hc) (cos_lt_cos_of_outside_arc hR hlo hhi)
  · by_contra hu
    have hlo : rightCutoffOuterRadius b δ ρ < |θ i - rightCutoffCenter b δ ρ| := by
      have hh := le_abs_self (θ i - rightCutoffCenter b δ ρ)
      linarith only [hu, hh, he.2.2.2]
    exact (not_lt_of_ge hc) (cos_lt_cos_of_outside_arc hR hlo hhi)

theorem rightCutoffProduct_weighted_jet_fundamental {b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) {N : ℕ}
    (w : (Fin N → ℝ) → ℂ) (k : ℕ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (-Real.pi) Real.pi)
    (hne : iteratedFDeriv ℝ k (fun x => w x * rightCutoffProduct b δ ρ N x) θ ≠ 0) :
    ∀ i, θ i ∈ Icc (-b - δ) (ρ + δ / 2) := by
  apply rightCutoffProduct_weighted_jet_rectangle h
    (L := -Real.pi) (by linarith [h.left_gap]) (by linarith [h.right_gap]) w k θ _ hne
  intro i
  simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hθ i

theorem rightCutoffProduct_weighted_jet_shifted {b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hreturn : 2 * ρ + δ / 2 < Real.pi) {N : ℕ}
    (w : (Fin N → ℝ) → ℂ) (k : ℕ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (-Real.pi - ρ) (Real.pi - ρ))
    (hne : iteratedFDeriv ℝ k (fun x => w x * rightCutoffProduct b δ ρ N x) θ ≠ 0) :
    ∀ i, θ i ∈ Icc (-b - δ) (ρ + δ / 2) := by
  apply rightCutoffProduct_weighted_jet_rectangle h
    (L := -Real.pi - ρ) (by linarith [h.left_gap, h.rho_pos]) (by linarith) w k θ _ hne
  intro i
  simpa only [show -Real.pi - ρ + 2 * Real.pi = Real.pi - ρ by ring] using hθ i

theorem rightCutoffProduct_weighted_jet_buffer {b δ ρ β : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hreturn : 2 * ρ + δ / 2 < Real.pi)
    (hδβ : δ ≤ β) (hρβ : ρ + δ / 2 ≤ β) {N : ℕ}
    (w : (Fin N → ℝ) → ℂ) (k : ℕ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (-Real.pi - ρ) (Real.pi - ρ))
    (hne : iteratedFDeriv ℝ k (fun x => w x * rightCutoffProduct b δ ρ N x) θ ≠ 0) :
    ∀ i, θ i ∈ Icc (-b - β) β := by
  have hh := rightCutoffProduct_weighted_jet_shifted h hreturn w k θ hθ hne
  intro i
  exact ⟨by linarith only [(hh i).1, hδβ], (hh i).2.trans hρβ⟩

end IsingBulk.AnisoF002.Isotropic

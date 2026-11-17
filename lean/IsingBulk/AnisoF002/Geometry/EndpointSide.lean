import IsingBulk.AnisoF002.Geometry.EndpointBoundary
import IsingBulk.AnisoF002.Geometry.EndpointCoordinate

/-!
# The actual spectral set occupies one side of a regular endpoint chart

F002 `prop:regular_dense`, proof after `eq:endpoint-defect`.
The defining equation is retained in its unsquared form throughout.
We first prove the exact Cramer/imaginary-part identity, then use actual
continuity to preserve the other strict cosine and exclude the opposite
endpoint in a common neighborhood.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set Filter
open scoped Topology

theorem mem_spectralSetF002_iff_cramer {lam : ℝ} {z : ℂ}
    (hdet : spectralDetF002 lam z ≠ 0) :
    z ∈ spectralSetF002 lam ↔
      cramerU lam z ∈ Set.Icc (-1 : ℝ) 1 ∧ cramerV lam z ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · rintro ⟨u, hu, v, hv, hinc⟩
    rw [cramerU_of_incidence hdet hinc, cramerV_of_incidence hdet hinc]
    exact ⟨hu, hv⟩
  · rintro ⟨hu, hv⟩
    exact ⟨cramerU lam z, hu, cramerV lam z, hv, cramer_incidence hdet⟩

theorem cramerV_endpoint_deviation {lam e : ℝ} {z : ℂ}
    (hdet : spectralDetF002 lam z ≠ 0) (hS : spectralS z ≠ 0) :
    spectralDetF002 lam z * (cramerV lam z - e) =
      Complex.normSq (spectralS z) * (edgeCoordinateF002 lam e z).im := by
  have hn : Complex.normSq (spectralS z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hS)
  unfold cramerV edgeCoordinateF002
  rw [Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  field_simp [hdet, hn]
  unfold spectralDetF002
  ring

theorem endpoint_interval_iff_one_sided {e v : ℝ} (he : e = 1 ∨ e = -1)
    (hfar : -1 < e * v) : v ∈ Set.Icc (-1 : ℝ) 1 ↔ e * v ≤ 1 := by
  constructor
  · intro hv
    rcases he with rfl | rfl <;> nlinarith [hv.1, hv.2]
  · intro hv
    rcases he with rfl | rfl <;> constructor <;> nlinarith

theorem signed_deviation_le_iff (D N e v g : ℝ) (hD : D ≠ 0) (hN : 0 < N)
    (he : e ^ 2 = 1) (hdev : D * (v - e) = N * g) :
    e * v ≤ 1 ↔ e * D * g ≤ 0 := by
  have hid : D ^ 2 * (e * v - 1) = N * (e * D * g) := by
    linear_combination e * D * hdev + D ^ 2 * he
  have hD2 : 0 < D ^ 2 := sq_pos_of_ne_zero hD
  constructor
  · intro hv
    have hh : D ^ 2 * (e * v - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD2.le (by linarith)
    rw [hid] at hh
    exact (mul_le_mul_iff_of_pos_left hN).mp (by simpa only [mul_zero] using hh)
  · intro hg
    have hh : N * (e * D * g) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hg
    rw [← hid] at hh
    have hv : e * v - 1 ≤ 0 :=
      (mul_le_mul_iff_of_pos_left hD2).mp (by simpa only [mul_zero] using hh)
    linarith

theorem mem_spectralSetF002_iff_signed_im {lam e : ℝ} {z : ℂ}
    (he : e = 1 ∨ e = -1)
    (hdet : spectralDetF002 lam z ≠ 0) (hS : spectralS z ≠ 0)
    (hu : cramerU lam z ∈ Set.Ioo (-1 : ℝ) 1)
    (hfar : -1 < e * cramerV lam z) :
    z ∈ spectralSetF002 lam ↔
      e * spectralDetF002 lam z * (edgeCoordinateF002 lam e z).im ≤ 0 := by
  rw [mem_spectralSetF002_iff_cramer hdet]
  have hU : cramerU lam z ∈ Set.Icc (-1 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  rw [and_iff_right hU, endpoint_interval_iff_one_sided he hfar]
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  exact signed_deviation_le_iff _ _ _ _ _ hdet (Complex.normSq_pos.mpr hS) he2
    (cramerV_endpoint_deviation hdet hS)

theorem eventually_signed_side_of_incidence {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hdet : spectralDetF002 lam z ≠ 0) (hS : spectralS z ≠ 0)
    (hu : |u| < 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    ∀ᶠ w in 𝓝 z, w ∈ spectralSetF002 lam ↔
      e * spectralDetF002 lam w * (edgeCoordinateF002 lam e w).im ≤ 0 := by
  have hu0 : cramerU lam z ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [cramerU_of_incidence hdet hinc]
    exact abs_lt.mp hu
  have hv0 : -1 < e * cramerV lam z := by
    rw [cramerV_of_incidence hdet hinc]
    rcases he with rfl | rfl <;> norm_num
  have hU : ∀ᶠ w in 𝓝 z, cramerU lam w ∈ Set.Ioo (-1 : ℝ) 1 :=
    (continuousAt_cramerU hdet).eventually (Ioo_mem_nhds hu0.1 hu0.2)
  have hV : ∀ᶠ w in 𝓝 z, -1 < e * cramerV lam w :=
    (continuousAt_const.mul (continuousAt_cramerV hdet)).eventually (Ioi_mem_nhds hv0)
  have hD : ∀ᶠ w in 𝓝 z, spectralDetF002 lam w ≠ 0 :=
    (continuous_spectralDetF002 lam).continuousAt.eventually_ne hdet
  have hS' : ∀ᶠ w in 𝓝 z, spectralS w ≠ 0 :=
    continuous_spectralS_f002.continuousAt.eventually_ne hS
  filter_upwards [hU, hV, hD, hS'] with w hwU hwV hwD hwS
  exact mem_spectralSetF002_iff_signed_im he hwD hwS hwU hwV

/-- The strict interior side of the physical spectral complement is identified
by the imaginary part of the actual nonramified endpoint coordinate. -/
theorem regular_first_endpoint_side {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : 0 < z.re)
    (hedge : geometryF1 lam z.re z.im = 0)
    (hsecond : geometryF2 lam z.re z.im ≠ 0) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ spectralDetF002 lam z ≠ 0 ∧
      HasDerivAt (edgeCoordinateF002 lam e) (edgeDerivativeF002 lam e z) z ∧
      edgeDerivativeF002 lam e z ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam ↔
        0 < e * spectralDetF002 lam w * (edgeCoordinateF002 lam e w).im) := by
  obtain ⟨hdet, u, e, hu, he, hinc⟩ :=
    regular_first_endpoint_exists hlam hx hedge hsecond
  have hS := spectralS_ne_zero_of_re_pos hx
  refine ⟨e, he, hdet, edgeCoordinate_hasDerivAt he hS,
    edgeDerivative_ne_zero hlam hx hu he hinc, ?_⟩
  filter_upwards [eventually_signed_side_of_incidence hdet hS hu he hinc] with w hw
  exact hw.not.trans not_le

end
end IsingBulk.AnisoF002.Geometry

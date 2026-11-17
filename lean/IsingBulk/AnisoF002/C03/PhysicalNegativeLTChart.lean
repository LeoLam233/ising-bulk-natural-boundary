import IsingBulk.AnisoF002.C03.PhysicalInwardComponent

/-!
# The actual negative endpoint chart for the even physical series

The angular translation by pi changes the transverse coefficient from
B to -B.  With negative spectral determinant, this coefficient has
positive imaginary part and the already proved complete regular mechanism
applies.  The inverse and its side are constructed from the literal
unsquared physical dispersion.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
  IsingBulk.AnisoF002.NegativeHT Filter Set
open scoped Topology

def negativeLTParameterF002 (lam b : ℝ) (z : ℂ) : ℂ :=
  edgeCoordinateF002 lam (-1) z - (b : ℂ)

theorem negativeLTParameterF002_center {lam b : ℝ} {z : ℂ}
    (hS : spectralS z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) - spectralT lam z) :
    negativeLTParameterF002 lam b z = 0 := by
  unfold negativeLTParameterF002
  rw [edgeCoordinate_eq_of_incidence hS (by simpa [sub_eq_add_neg] using hinc), sub_self]

theorem negativeLT_dispersion_literal {lam b : ℝ} {z t q : ℂ}
    (hS : spectralS z ≠ 0) (ht : negativeLTParameterF002 lam b z = t) :
    (spectralA lam z - spectralT lam z * Complex.cos (q + Real.pi)) / spectralS z =
      affineEdgeCenter b t + (-spectralRatioF002 lam z) * (1 - Complex.cos q) := by
  rw [← ht, Complex.cos_add_pi]
  unfold negativeLTParameterF002 edgeCoordinateF002 affineEdgeCenter spectralRatioF002
  push_cast
  field_simp
  ring

theorem exists_negativeLT_physical_edge_control {lam b : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z < 0) :
    ∃ (Z B : ℂ → ℂ) (_d : RegularEdgeCompleteControl b B),
      AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧
      HasDerivAt Z (edgeDerivativeF002 lam (-1) z)⁻¹ 0 ∧
      AnalyticAt ℂ B 0 ∧ B 0 = -(spectralT lam z / spectralS z) ∧
      (∀ t, B t = -(spectralT lam (Z t) / spectralS (Z t))) ∧
      (∀ᶠ t in 𝓝 0, negativeLTParameterF002 lam b (Z t) = t ∧ spectralS (Z t) ≠ 0 ∧
        ∀ q : ℂ, (spectralA lam (Z t) - spectralT lam (Z t) * Complex.cos (q + Real.pi)) /
          spectralS (Z t) = affineEdgeCenter b t + B t * (1 - Complex.cos q)) ∧
      (∀ᶠ w in 𝓝 z, Z (negativeLTParameterF002 lam b w) = w) := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hpa : AnalyticAt ℂ (negativeLTParameterF002 lam b) z :=
    (analyticAt_edgeCoordinateF002 (e := -1) hS).sub analyticAt_const
  have hpd : HasDerivAt (negativeLTParameterF002 lam b) (edgeDerivativeF002 lam (-1) z) z :=
    (edgeCoordinate_hasDerivAt (lam := lam) (Or.inr rfl) hS).sub_const _
  have hd0 : edgeDerivativeF002 lam (-1) z ≠ 0 :=
    edgeDerivative_ne_zero_all_re hlam hx hb (Or.inr rfl) (by simpa [sub_eq_add_neg] using hinc)
  obtain ⟨Z, hZa, hZ0, hZd, hright, hleft⟩ := exists_local_analytic_inverse_zero
    hpa hpd hd0 (negativeLTParameterF002_center hS hinc)
  let B : ℂ → ℂ := fun t => -spectralRatioF002 lam (Z t)
  have hBa : AnalyticAt ℂ B 0 :=
    ((analyticAt_spectralRatioF002 hS).comp_of_eq hZa hZ0).neg
  have hB0 : B 0 = -(spectralT lam z / spectralS z) := by
    simp only [B, hZ0, spectralRatioF002]
  have hBim : 0 < (B 0).im := by
    change 0 < (-spectralRatioF002 lam (Z 0)).im
    rw [hZ0, Complex.neg_im, spectralRatioF002_im]
    exact neg_pos.mpr (div_neg_of_neg_of_pos hdet (Complex.normSq_pos.mpr hS))
  obtain ⟨d⟩ := exists_regular_edge_complete_control hBa hb hBim
  refine ⟨Z, B, d, hZa, hZ0, hZd, hBa, hB0, fun _ => rfl, ?_, hleft⟩
  have hS' : ∀ᶠ t in 𝓝 0, spectralS (Z t) ≠ 0 :=
    ((analyticAt_spectralS_f002 z).comp_of_eq hZa hZ0).continuousAt.eventually_ne
      (by simpa only [Function.comp_def, hZ0] using hS)
  filter_upwards [hright, hS'] with t ht hs
  exact ⟨ht, hs, fun q => negativeLT_dispersion_literal hs ht⟩

theorem negativeLT_physical_coordinate_side {lam b : ℝ} {z : ℂ}
    (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z < 0) :
    ∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam ↔ 0 < (negativeLTParameterF002 lam b w).im := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hs := eventually_signed_side_of_incidence hdet.ne hS hb (Or.inr rfl)
    (by simpa [sub_eq_add_neg] using hinc)
  have hd := (continuous_spectralDetF002 lam).continuousAt.eventually (Iio_mem_nhds hdet)
  filter_upwards [hs, hd] with w hw hwd
  rw [hw, not_le]
  simp only [neg_one_mul, negativeLTParameterF002, Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact mul_pos_iff_of_pos_left (neg_pos.mpr hwd)

theorem negativeLT_physical_chart_inward_domain {lam b : ℝ} {z : ℂ} {Z : ℂ → ℂ} {D : Set ℂ}
    (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z < 0)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D)
    (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hright : ∀ᶠ t in 𝓝 (0 : ℂ), negativeLTParameterF002 lam b (Z t) = t)
    (hleft : ∀ᶠ w in 𝓝 z, Z (negativeLTParameterF002 lam b w) = w) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∈ D := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  apply local_inverse_inward_mem_domain hD hDC (by simpa only [compl_compl] using hfront) hz
    ((analyticAt_edgeCoordinateF002 (e := -1) hS).sub analyticAt_const).continuousAt
    (negativeLTParameterF002_center hS hinc) hZ hZ0 hright hleft
  exact negativeLT_physical_coordinate_side hx hb hinc hdet

theorem negativeLT_edgeAngleRoot_eq_canonical {lam b : ℝ} {Z B : ℂ → ℂ} {t : ℂ}
    (hS : spectralS (Z t) ≠ 0)
    (hdisp : ∀ q : ℂ,
      (spectralA lam (Z t) - spectralT lam (Z t) * Complex.cos (q + Real.pi)) / spectralS (Z t) =
        affineEdgeCenter b t + B t * (1 - Complex.cos q))
    (hphase : ∀ q : ℝ, 0 < (edgeAnglePhase (affineEdgeCenter b) B t q).re) :
    ∀ q : ℝ, edgeAngleRoot (affineEdgeCenter b) B t q =
      spectralSmallRootF002 lam (Z t) (q + Real.pi) := by
  intro q
  rw [← edgeAnglePhase_exp_neg]
  apply phase_exp_eq_spectralSmallRoot hS
  · rw [edgeAnglePhase_cosh]
    simpa only [← Complex.ofReal_add, ← Complex.ofReal_cos] using (hdisp (q : ℂ)).symm
  · exact hphase q

end
end IsingBulk.AnisoF002.RegularTail.C03

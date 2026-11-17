import IsingBulk.AnisoF002.Geometry.CanonicalRootAnalytic
import Mathlib.Topology.Order.Compact

/-!
# Gluing and compact modulus gaps of the F002 spectral root

The local polynomial inverse constructed in `CanonicalRootAnalytic` is
identified with the unique canonical root. This proves holomorphy on the
actual unsquared spectral complement and joint continuity in real angle,
including zero-S fibers. Compactness then gives a gap uniform in every
real angle, using the cosine parameter to cover the angular circle.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Filter Set
open scoped Topology

theorem spectralSmallRootF002_analyticAt {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    AnalyticAt ℂ (fun w => spectralSmallRootF002 lam w q) z := by
  obtain ⟨R, hR, _, he⟩ := exists_joint_analytic_spectral_root q hz
  have hinj : AnalyticAt ℂ (fun w : ℂ => (w, (q : ℂ))) z :=
    analyticAt_id.prod analyticAt_const
  have hlocal : AnalyticAt ℂ (fun w => R (w, (q : ℂ))) z := hR.comp_of_eq hinj rfl
  have hpoly := hinj.continuousAt.eventually he
  have hcomp : ∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam :=
    (isClosed_spectralSetF002 lam).isOpen_compl.mem_nhds hz
  apply hlocal.congr
  filter_upwards [hpoly, hcomp] with w hw hwc
  apply spectralSmallRootF002_unique q hwc
  · simpa only [spectralRootPolynomialF002, ← Complex.ofReal_cos] using hw.1
  · exact hw.2

theorem spectralSmallRootF002_analyticOnNhd (lam q : ℝ) :
    AnalyticOnNhd ℂ (fun z => spectralSmallRootF002 lam z q) (spectralSetF002 lam)ᶜ :=
  fun _ hz => spectralSmallRootF002_analyticAt q hz

theorem spectralSmallRootF002_continuousAt {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    ContinuousAt (fun a : ℂ × ℝ => spectralSmallRootF002 lam a.1 a.2) (z, q) := by
  obtain ⟨R, hR, _, he⟩ := exists_joint_analytic_spectral_root q hz
  have hinj : ContinuousAt (fun a : ℂ × ℝ => (a.1, (a.2 : ℂ))) (z, q) :=
    continuousAt_fst.prodMk (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd)
  have hlocal : ContinuousAt (fun a : ℂ × ℝ => R (a.1, (a.2 : ℂ))) (z, q) :=
    hR.continuousAt.comp_of_eq hinj rfl
  have hpoly := hinj.eventually he
  have hc : ∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam :=
    (isClosed_spectralSetF002 lam).isOpen_compl.mem_nhds hz
  have hcomp : ∀ᶠ a : ℂ × ℝ in 𝓝 (z, q), a.1 ∉ spectralSetF002 lam :=
    (show ContinuousAt (fun a : ℂ × ℝ => a.1) (z, q) from continuousAt_fst).eventually hc
  apply hlocal.congr
  filter_upwards [hpoly, hcomp] with a ha hca
  apply spectralSmallRootF002_unique a.2 hca
  · simpa only [spectralRootPolynomialF002, ← Complex.ofReal_cos] using ha.1
  · exact ha.2

theorem spectralSmallRootF002_eq_of_cos_eq {lam : ℝ} {z : ℂ} {q t : ℝ}
    (hz : z ∉ spectralSetF002 lam) (hqt : Real.cos q = Real.cos t) :
    spectralSmallRootF002 lam z q = spectralSmallRootF002 lam z t := by
  apply spectralSmallRootF002_unique t hz
  · simpa only [spectralRootPolynomialF002, hqt] using (spectralSmallRootF002_spec q hz).1
  · exact (spectralSmallRootF002_spec q hz).2

theorem spectralSmallRootF002_eq_zero {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z = 0) :
    spectralSmallRootF002 lam z q = 0 := by
  symm
  apply spectralSmallRootF002_unique q hz
  · simp [spectralRootPolynomialF002, hS]
  · norm_num

/-- The strict disk gap is uniform on every compact parameter set and over
the entire real angle circle, with no excluded zero-S parameter. -/
theorem spectralSmallRootF002_compact_gap {lam : ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hsub : K ⊆ (spectralSetF002 lam)ᶜ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ z ∈ K, ∀ q : ℝ, ‖spectralSmallRootF002 lam z q‖ ≤ ρ := by
  by_cases hne : K.Nonempty
  · let Q := Set.Icc (0 : ℝ) Real.pi
    have hQ : IsCompact Q := isCompact_Icc
    have hQne : Q.Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
    have hcont : ContinuousOn (fun a : ℂ × ℝ => ‖spectralSmallRootF002 lam a.1 a.2‖)
        (K ×ˢ Q) := by
      intro a ha
      exact (spectralSmallRootF002_continuousAt a.2 (hsub ha.1)).norm.continuousWithinAt
    obtain ⟨a, ha, hmax⟩ := (hK.prod hQ).exists_isMaxOn (hne.prod hQne) hcont
    refine ⟨‖spectralSmallRootF002 lam a.1 a.2‖, norm_nonneg _,
      (spectralSmallRootF002_spec a.2 (hsub ha.1)).2, ?_⟩
    intro z hz q
    have hcos : Real.cos q = Real.cos (Real.arccos (Real.cos q)) :=
      (Real.cos_arccos (Real.neg_one_le_cos q) (Real.cos_le_one q)).symm
    rw [spectralSmallRootF002_eq_of_cos_eq (hsub hz) hcos]
    exact (isMaxOn_iff.mp hmax) (z, Real.arccos (Real.cos q))
      (show (z, Real.arccos (Real.cos q)) ∈ K ×ˢ Q from
      ⟨hz, Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

end
end IsingBulk.AnisoF002.Geometry

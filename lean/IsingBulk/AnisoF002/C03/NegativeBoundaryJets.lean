import IsingBulk.AnisoF002.C03.NegativeCoefficientJets
import IsingBulk.AnisoF002.C03.NegativeInwardDisk
import IsingBulk.AnisoF002.C03.NegativePhysicalCoefficient

/-!
# Boundary jets of the complete physical odd particle series

The complete sum is differentiated on genuine common inward disks.  Its
boundary limits then follow from the summable coefficient jet bounds.
The physical-root normalization is preserved, and every odd particle is
included.  This proves the jet interface, not Taylor noncancellation.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def negativeCanonicalOddSum (B : ℂ → ℂ) (φ : ℝ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, negativeCanonicalCoefficient B φ (2 * n) t

def negativePhysicalOddSum (b B : ℂ → ℂ) (φ : ℝ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, negativePhysicalCoefficient b B φ (2 * n) t

namespace NegativeCoefficientControl
variable {B : ℂ → ℂ} {φ : ℝ} (d : NegativeCoefficientControl B φ)

theorem oddSum_analytic_inward {eps : ℝ} (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    AnalyticAt ℂ (negativeCanonicalOddSum B φ) (-(eps : ℂ)) := by
  obtain ⟨r, hr, M, hM, hf, hb⟩ := d.exists_odd_common_disk_majorant he he0
  exact analyticAt_tsum_of_common_disk hr hM hf hb

theorem oddSum_iteratedDeriv_inward (j : ℕ) {eps : ℝ} (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    iteratedDeriv j (negativeCanonicalOddSum B φ) (-(eps : ℂ)) =
      ∑' n : ℕ, iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) (-(eps : ℂ)) := by
  obtain ⟨r, hr, M, hM, hf, hb⟩ := d.exists_odd_common_disk_majorant he he0
  exact iteratedDeriv_tsum_of_common_disk hr hM hf hb (Metric.mem_ball_self (half_pos hr)) j

include d in
theorem oddSum_boundary_jet_limit (j : ℕ) :
    Tendsto (fun eps : ℝ => iteratedDeriv j (negativeCanonicalOddSum B φ) (-(eps : ℂ)))
      (𝓝[>] 0) (𝓝 (∑' n : ℕ, iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0)) := by
  have hlim := (d.odd_coefficient_jet_boundary_limit j).mono_left
    (nhdsWithin_mono 0 (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds d.eps0_pos)]
    with eps he he0
  exact (d.oddSum_iteratedDeriv_inward j he he0.le).symm

end NegativeCoefficientControl

theorem eventuallyEq_iteratedDeriv {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) (j : ℕ) : iteratedDeriv j f =ᶠ[𝓝 z] iteratedDeriv j g := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ j ih => simpa only [Filter.EventuallyEq, iteratedDeriv_succ] using ih.deriv

theorem physical_oddSum_boundary_jets {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) (j : ℕ) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0‖) ∧
      Tendsto (fun eps : ℝ => iteratedDeriv j (negativePhysicalOddSum b B φ) (-(eps : ℂ)))
        (𝓝[>] 0)
        (𝓝 (∑' n : ℕ, iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0)) := by
  obtain ⟨d⟩ := exists_negative_coefficient_control hB hφ hπ hBi
  obtain ⟨ζ, _, hζ, he⟩ := eventually_physical_odd_coefficients φ hb hB hBi hbsq
  have hcoeff (n : ℕ) : iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0 =
      ζ * iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0 := by
    have heq : negativePhysicalCoefficient b B φ (2 * n) =ᶠ[𝓝 0]
        (fun t => ζ * negativeCanonicalCoefficient B φ (2 * n) t) :=
      he.mono fun t ht => ht (2 * n) ⟨n, rfl⟩
    rw [heq.iteratedDeriv_eq j, iteratedDeriv_const_mul_field]
  have hwhole : negativePhysicalOddSum b B φ =ᶠ[𝓝 0]
      (fun t => ζ * negativeCanonicalOddSum B φ t) := by
    filter_upwards [he] with t ht
    unfold negativePhysicalOddSum negativeCanonicalOddSum
    simp_rw [ht (2 * _) ⟨_, rfl⟩]
    exact tsum_mul_left
  have hnorm (n : ℕ) : ‖iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0‖ =
      ‖iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0‖ := by
    rw [hcoeff n, norm_mul, hζ, one_mul]
  refine ⟨(d.odd_boundary_jets_summable j).congr (fun n => (hnorm n).symm), ?_⟩
  have hD := eventuallyEq_iteratedDeriv hwhole j
  have hD' : ∀ᶠ t in 𝓝 (0 : ℂ),
      iteratedDeriv j (negativePhysicalOddSum b B φ) t =
        ζ * iteratedDeriv j (negativeCanonicalOddSum B φ) t := by
    filter_upwards [hD] with t ht
    simpa only [iteratedDeriv_const_mul_field] using ht
  have hpath : Tendsto (fun eps : ℝ => -(eps : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, neg_zero] using
      ((Complex.continuous_ofReal.tendsto (0 : ℝ)).neg.mono_left nhdsWithin_le_nhds)
  have hlim := (d.oddSum_boundary_jet_limit j).const_mul ζ
  have hsum : (∑' n : ℕ, iteratedDeriv j (negativePhysicalCoefficient b B φ (2 * n)) 0) =
      ζ * ∑' n : ℕ, iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0 := by
    simp_rw [hcoeff]
    exact tsum_mul_left
  rw [hsum]
  apply hlim.congr'
  filter_upwards [hpath.eventually hD'] with eps heq
  exact heq.symm

end
end IsingBulk.AnisoF002.NegativeHT

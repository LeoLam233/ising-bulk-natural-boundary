import IsingBulk.AnisoF002.C03.RegularRationalFirst
import IsingBulk.AnisoF002.C03.RegularAmplitudePeriod
import IsingBulk.Anisotropic.Final.LocalExtension

/-!
# Nonextension from the actual complete regular first singularity

The generic argument compares derivatives of an alleged analytic germ
with the proved nonzero scaled limit.  The only historical object used
is the already inspected literal definition HasDomainExtension; no
historical nonextension or first-singularity theorem is invoked.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic
open scoped Topology

theorem positive_square_tendsto_zero :
    Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : ContinuousAt (fun s : ℝ => s ^ 2) 0 := by fun_prop
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 0 < s ^ 2
    exact sq_pos_of_pos (show 0 < s from hs)

theorem no_analytic_inward_germ_of_scaled_limit {f : ℂ → ℂ} {A : ℂ} {j l : ℕ}
    (hl : 0 < l) (hA : A ≠ 0)
    (hlim : Tendsto (fun s : ℝ => (s : ℂ) ^ l * iteratedDeriv j f
      (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), f =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g := by
  rintro ⟨g, hg, heq⟩
  have hg0 := (analytic_scaled_jet_zero hg j l hl).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hgA : Tendsto (fun s : ℝ => (s : ℂ) ^ l * iteratedDeriv j g
      (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    apply hlim.congr'
    filter_upwards [positive_square_tendsto_zero.eventually heq] with s hs
    rw [hs.iteratedDeriv_eq j]
  exact hA (tendsto_nhds_unique hgA hg0)

theorem no_upper_domain_extension_of_scaled_limit {f : ℂ → ℂ} {A : ℂ} {j l : ℕ}
    (hl : 0 < l) (hA : A ≠ 0)
    (hlim : Tendsto (fun s : ℝ => (s : ℂ) ^ l * iteratedDeriv j f
      (((s ^ 2 : ℝ) : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    ¬ HasDomainExtension {u : ℂ | 0 < u.im} f 0 := by
  rintro ⟨U, hU, h0, g, hg, heq⟩
  apply no_analytic_inward_germ_of_scaled_limit hl hA hlim
  refine ⟨g, hg 0 h0, ?_⟩
  have hp : Tendsto (fun eps : ℝ => (eps : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    convert (show ContinuousAt (fun eps : ℝ => (eps : ℂ) * Complex.I) 0 by fun_prop).tendsto using 1
    simp
  have hnear := hp.eventually (hU.mem_nhds h0)
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with eps he heU
  have heI : (eps : ℂ) * Complex.I ∈ {u : ℂ | 0 < u.im} := by simpa using he
  filter_upwards [hU.mem_nhds heU, hopen.mem_nhds heI] with u hu hup
  exact (heq ⟨hu, hup⟩).symm

theorem regularFirstAmplitude_odd_ne_zero_of_odd {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) {n : ℕ} (hn : Odd (n + 1)) (hn0 : 0 < n) :
    regularFirstAmplitude b a n (oddTopOrder (n + 1)) ≠ 0 := by
  obtain ⟨k, hk⟩ := hn
  have hnEq : n = 2 * k := by omega
  have hk0 : 0 < k := by omega
  subst n
  exact regularFirstAmplitude_odd_ne_zero hb ha hk0

namespace RegularEdgeCompleteControl

theorem rational_odd_series_no_analytic_inward_germ {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    {a : ℂ → ℂ} (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a 0
          =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g := by
  have hp0 : p - 1 + 1 = p := by omega
  have hA := regularFirstAmplitude_odd_ne_zero_of_odd
    (regularRational_cos_abs_lt_one hr hrp) ha
    (by rw [hp0]; exact hp) (by omega : 0 < p - 1)
  rw [hp0] at hA
  exact no_analytic_inward_germ_of_scaled_limit (by norm_num : 0 < 2) hA
    (d.rational_odd_series_first_limit hr hrp hcop hp ha)

theorem rational_odd_series_no_upper_extension {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    {a : ℂ → ℂ} (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) :
    ¬ HasDomainExtension {u : ℂ | 0 < u.im}
      (edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a 0) 0 := by
  have hp0 : p - 1 + 1 = p := by omega
  have hA := regularFirstAmplitude_odd_ne_zero_of_odd
    (regularRational_cos_abs_lt_one hr hrp) ha
    (by rw [hp0]; exact hp) (by omega : 0 < p - 1)
  rw [hp0] at hA
  exact no_upper_domain_extension_of_scaled_limit (by norm_num : 0 < 2) hA
    (d.rational_odd_series_first_limit hr hrp hcop hp ha)

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03

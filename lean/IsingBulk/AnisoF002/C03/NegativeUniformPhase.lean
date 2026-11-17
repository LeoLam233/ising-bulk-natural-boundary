import IsingBulk.AnisoF002.C03.NegativePhysicalBranch
import IsingBulk.AnisoF002.NegativeHT.MovingPoleDifferential

/-!
# One actual negative-edge phase before the particle number

The inverse of cosh is chosen once at the limiting edge and composed with
the literal physical dispersion.  Its center and parity identities are
exact identities of this single function, for every displacement.  A
common analytic neighborhood is then chosen before any particle number.
This removes the varying-branch issue in the fixed-n implicit construction;
it does not yet assert a dimension-uniform moving-pole radius or density.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology BigOperators

theorem localNegativeDispersion_analyticAt {B : ℂ → ℂ} {φ : ℝ} {a : ℂ × ℂ}
    (hB : AnalyticAt ℂ B a.1) : AnalyticAt ℂ (localNegativeDispersion B φ) a := by
  have hb : AnalyticAt ℂ (fun a : ℂ × ℂ => B a.1) a := hB.comp analyticAt_fst
  exact analyticAt_const.add (hb.mul
    (analyticAt_fst.sub (analyticAt_const.sub (Complex.analyticAt_cos.comp analyticAt_snd))))

theorem exists_uniform_negative_phase {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : Real.sin φ ≠ 0) :
    ∃ g : ℂ × ℂ → ℂ,
      (∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I) ∧
      (∀ t δ : ℂ, g (t, -δ) = g (t, δ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ a ∈ Metric.ball (0, 0) r,
          AnalyticAt ℂ g a ∧ Complex.cosh (g a) = localNegativeDispersion B φ a := by
  obtain ⟨G, hG, hGc, _, hGi⟩ := exists_local_cosh_inverse φ hφ
  let g : ℂ × ℂ → ℂ := G ∘ localNegativeDispersion B φ
  have hw0 : localNegativeDispersion B φ (0, 0) = (Real.cos φ : ℂ) := by
    simp [localNegativeDispersion]
  have hWa := localNegativeDispersion_analyticAt (φ := φ) (a := (0, 0)) hB
  have hga : AnalyticAt ℂ g (0, 0) := hG.comp_of_eq hWa hw0
  have he : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a := by
    exact (show Tendsto (localNegativeDispersion B φ) (𝓝 (0, 0))
      (𝓝 (Real.cos φ : ℂ)) by simpa only [hw0] using hWa.continuousAt.tendsto).eventually hGi
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp
    (hga.eventually_analyticAt.and he)
  refine ⟨g, ?_, ?_, r, hr, ?_⟩
  · intro δ
    change G (localNegativeDispersion B φ (1 - Complex.cos δ, δ)) = _
    simpa [localNegativeDispersion] using hGc
  · intro t δ
    simp [g, Function.comp_def, localNegativeDispersion, Complex.cos_neg]
  · intro a ha
    exact hall (Metric.mem_ball.mp ha)

/-- A single analytic physical phase, with exact center identities and
canonical small-root identification on the inward real side.  The sign
condition is the orientation of the chosen negative edge, not a new
physical premise in the terminal theorem. -/
theorem exists_uniform_negative_physical_phase {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hφ0 : 0 < φ) (hφpi : φ < Real.pi)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1))
    (hside : (spectralT lam z / spectralS z).im < 0) :
    ∃ (Z B : ℂ → ℂ) (g : ℂ × ℂ → ℂ),
      AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ AnalyticAt ℂ B 0 ∧
      B 0 = spectralT lam z / spectralS z ∧ B 0 ≠ 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I) ∧
      (∀ t δ : ℂ, g (t, -δ) = g (t, δ)) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ a ∈ Metric.ball (0, 0) r,
        AnalyticAt ℂ g a ∧ spectralS (Z a.1) ≠ 0 ∧
        Complex.cosh (g a) = localNegativeDispersion B φ a ∧
        Complex.cosh (g a) =
          (spectralA lam (Z a.1) - spectralT lam (Z a.1) *
            Complex.cos ((Real.pi : ℂ) + a.2)) / spectralS (Z a.1)) ∧
      (∀ᶠ a : ℝ × ℝ in 𝓝 (0, 0), a.1 < 0 →
        0 < (g (realPairToComplex a)).re ∧
        Complex.exp (-g (realPairToComplex a)) =
          spectralSmallRootF002 lam (Z (a.1 : ℂ)) (Real.pi + a.2)) ∧
      (∀ᶠ t in 𝓝 0, negativeParameterF002 lam (Real.cos φ) (Z t) = t) ∧
      (∀ᶠ w in 𝓝 z, Z (negativeParameterF002 lam (Real.cos φ) w) = w) := by
  have hφ : Real.sin φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi)
  obtain ⟨Z, B, hZa, hZ0, hBa, hB0, hBne, hBe, hp, hleft⟩ :=
    exists_negative_physical_chart hlam hx (abs_cos_lt_one_of_sin_ne_zero hφ) hinc
  obtain ⟨g, hgcent, hgeven, r, hr, hgball⟩ := exists_uniform_negative_phase hBa hφ
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by simpa using hgcent 0
  have hga : AnalyticAt ℂ g (0, 0) :=
    (hgball (0, 0) (Metric.mem_ball_self hr)).1
  have hball : ∀ᶠ a : ℂ × ℂ in 𝓝 (0, 0), a ∈ Metric.ball (0, 0) r :=
    Metric.ball_mem_nhds _ hr
  have hge : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a :=
    hball.mono (fun a ha => (hgball a ha).2)
  have hproj : Tendsto (fun a : ℂ × ℂ => a.1) (𝓝 (0, 0)) (𝓝 0) :=
    continuous_fst.continuousAt
  have hphysical : ∀ᶠ a in 𝓝 (0, 0), spectralS (Z a.1) ≠ 0 ∧
      Complex.cosh (g a) =
        (spectralA lam (Z a.1) - spectralT lam (Z a.1) *
          Complex.cos ((Real.pi : ℂ) + a.2)) / spectralS (Z a.1) := by
    filter_upwards [hge, hproj.eventually hp] with a ha hp'
    refine ⟨hp'.2.1, ?_⟩
    rw [ha, hp'.2.2.2 a.2]
    unfold localNegativeDispersion
    ring
  have hneighborhood : ∀ᶠ a in 𝓝 (0, 0), AnalyticAt ℂ g a ∧
      spectralS (Z a.1) ≠ 0 ∧ Complex.cosh (g a) = localNegativeDispersion B φ a ∧
      Complex.cosh (g a) =
        (spectralA lam (Z a.1) - spectralT lam (Z a.1) *
          Complex.cos ((Real.pi : ℂ) + a.2)) / spectralS (Z a.1) := by
    filter_upwards [hga.eventually_analyticAt, hge, hphysical] with a ha he hp'
    exact ⟨ha, hp'.1, he, hp'.2⟩
  obtain ⟨r', hr', hall⟩ := Metric.eventually_nhds_iff.mp hneighborhood
  refine ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hgcent, hgeven,
    ⟨r', hr', fun a ha => hall (Metric.mem_ball.mp ha)⟩, ?_,
    hp.mono (fun _ h => h.1), hleft⟩
  have hc : Tendsto realPairToComplex (𝓝 (0, 0)) (𝓝 (0, 0)) :=
    continuous_realPairToComplex.continuousAt
  have hpos := negative_phase_re_pos_near_inward hBa.continuousAt
    (show (B 0).im < 0 by simpa only [hB0] using hside)
    hga.continuousAt hg0 hφ0 hφpi hge
  filter_upwards [hpos, hc.eventually hphysical] with a ha hp'
  intro ht
  refine ⟨ha ht, phase_exp_eq_spectralSmallRoot hp'.1 ?_ (ha ht)⟩
  simpa only [realPairToComplex, Complex.ofReal_add, Complex.ofReal_cos] using hp'.2

/-- The same phase is analytic at all sufficiently late exact winding
centers.  No new inverse branch is chosen when n varies. -/
theorem eventually_uniform_negative_phase_centers {g : ℂ × ℂ → ℂ} {φ : ℝ}
    (hga : AnalyticAt ℂ g (0, 0))
    (hcenter : ∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I) :
    ∀ᶠ n : ℕ in atTop,
      AnalyticAt ℂ g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) ∧
      g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) = (φ : ℂ) * Complex.I := by
  have ht : Tendsto (fun n : ℕ => (windingTau n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_windingTau_zero
  have hd : Tendsto (fun n : ℕ => ((Real.pi / (n : ℝ) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat Real.pi)
  have hc := (ht.prodMk_nhds hd).eventually hga.eventually_analyticAt
  filter_upwards [hc] with n hn
  refine ⟨hn, ?_⟩
  simpa only [windingTau, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_cos] using hcenter ((Real.pi / (n : ℝ) : ℝ) : ℂ)

end
end IsingBulk.AnisoF002.NegativeHT

import IsingBulk.Anisotropic.NegativeDominance.PhysicalJetObstruction
import IsingBulk.Anisotropic.NegativeDominance.PaperPhysicalPrefactor
import IsingBulk.Anisotropic.NegativeDominance.NegativePaperInside

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter Metric FormFactors RegularEdges
open scoped Topology

def negativePaperCoefficient (lam : ℝ) (zeta A : ℂ → ℂ) (j : ℕ) : ℂ :=
  (∑' n : ℕ, iteratedDeriv j (fun t => A t^(2*n+1)*
    continuedAngularCoefficient (2*n) lam (zeta t)) 0)/(j.factorial:ℂ)

theorem negativePaperCoefficient_eq_tsum (lam : ℝ) (zeta A : ℂ → ℂ) (j : ℕ) :
    negativePaperCoefficient lam zeta A j=∑' n : ℕ,
      iteratedDeriv j (fun t => A t^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta t)) 0/
        (j.factorial:ℂ) := by
  unfold negativePaperCoefficient
  exact (tsum_div_const).symm

/-- All normalization and physical branch transfers for a proved zero-radius
complete negative-edge coefficient series. The radius premise is isolated as
an internal assembly input, not a published or physical-entry interface. -/
theorem negative_paper_chart_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hd : spectralDet lam z<0) (hu : |spectralU lam z|<1)
    {zeta A Z f : ℂ → ℂ} {r : ℝ} (hr : 0<r) (hZ0 : Z 0=z) (hf0 : f 0=0)
    (hZ : AnalyticOnNhd ℂ Z (ball 0 r)) (hf : AnalyticAt ℂ f 0)
    (hzeta : zeta=(fun t => Z (f t))) (hA : AnalyticAt ℂ A 0)
    (hmap : ∀u∈ball 0 r,0<u.im → Z u∈omegaH lam\{0})
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0, f (-(ε:ℂ))∈ball 0 r ∧ 0<(f (-(ε:ℂ))).im)
    (hjets : ∀ j : ℕ, Tendsto (fun ε : ℝ => iteratedDeriv j
      (fun t => A t*∑' n : ℕ, (spectralProduct lam (zeta t))^n*
        unscaledFullCoefficient (2*n+1) lam (zeta t)) (-(ε:ℂ))) (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, iteratedDeriv j (fun t => A t^(2*n+1)*
        continuedAngularCoefficient (2*n) lam (zeta t)) 0)))
    (hzero : (FormalMultilinearSeries.ofScalars ℂ (negativePaperCoefficient lam zeta A)).radius=0) :
    ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  obtain ⟨D,b,hD,hb,hb0,hm,hbranch,hinside⟩ := exists_paper_physical_prefactor hlam hr hZ
    (by simpa only [hZ0] using hd.ne) (by simpa only [hZ0] using hu)
    (fun u hu => (hmap u hu.1 hu.2).1) hf hf0 hin
  have hza : AnalyticAt ℂ zeta 0 := by
    rw [hzeta]
    exact (hZ 0 (mem_ball_self hr)).fun_comp_of_eq (f := f) hf hf0
  have hz0 : zeta 0=z := by simp only [hzeta,hf0,hZ0]
  have hp : Tendsto (fun ε : ℝ => -(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => -(ε:ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply high_no_extension_of_chart_jets_zero_radius hD hza hz0
    (by simpa only [hzeta] using hm) hA hb hb0
    (by simpa only [hzeta] using hbranch) hp hinside (negativePaperCoefficient lam zeta A) _ hzero
  intro j
  exact (hjets j).div_const _

end
end IsingBulk.Anisotropic.NegativeDominance

import IsingBulk.Anisotropic.RegularEdges.ScaledPhysicalTail

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter
open scoped Topology

theorem physicalParity_tail_inward_majorants
    {lam b : ℝ} {B S A zeta : ℂ→ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀u∈U,zeta u∉spectralSet lam) (hS0 : ∀u∈U,spectralS (zeta u)≠0)
    (hB : ∀u∈U,B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U,S u=spectralS (zeta u))
    (he : ∀u∈U,edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
    (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im) (hlam : 0<lam)
    (hphysical : ∀u∈U,zeta u∈(omegaH lam\{0})∪omegaL lam)
    (hAsq : ∀u∈U,(A u)^2=spectralProduct lam (zeta u))
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U) (j : ℕ) :
    ∃ Ghigh Glow : ℕ→ℝ,Summable Ghigh ∧ Summable Glow ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,∀n,
      ‖iteratedDeriv j (fun v => A v*(spectralProduct lam (zeta v))^(j+2+n)*
        FormFactors.unscaledFullCoefficient (2*(j+2+n)+1) lam (zeta v)) (Complex.I*(t:ℂ)^2)‖≤Ghigh n ∧
      ‖iteratedDeriv j (fun v => (spectralProduct lam (zeta v))^(j+2+n)*
        FormFactors.unscaledFullCoefficient (2*(j+2+n)) lam (zeta v)) (Complex.I*(t:ℂ)^2)‖≤Glow n := by
  obtain ⟨δ,hδ,Ghigh,Glow,hH,hL,hbound⟩ := physicalParity_tail_summable_jet_majorants_upper
    hb hB0 hBa hSa hSzero hAa0 hA0 hU ha hAa hz hS0 hB hS he hup hBi hlam hphysical hAsq j
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hnorm := htend.norm
  simp only [norm_zero] at hnorm
  refine ⟨Ghigh,Glow,hH,hL,?_⟩
  filter_upwards [self_mem_nhdsWithin,hin,hnorm.eventually (eventually_lt_nhds hδ)] with t ht htU htδ
  have him : 0<(Complex.I*(t:ℂ)^2).im := by
    rw [←Complex.ofReal_pow]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    exact sq_pos_of_pos ht
  exact hbound _ him htδ htU

end
end IsingBulk.Anisotropic.RegularEdges

import IsingBulk.Anisotropic.RegularEdges.ScaledPositiveMajorant
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularIdentity
noncomputable section
open Set Filter
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

theorem unscaledFullCoefficient_eq_angular_physical (n : ℕ) {lam : ℝ} (hlam : 0<lam)
    {z : ℂ} (hz : z∈(omegaH lam\{0})∪omegaL lam) :
    FormFactors.unscaledFullCoefficient (n+1) lam z=unscaledAngularCoefficient n lam z := by
  rcases hz with h|h
  · exact unscaledFullCoefficient_eq_angular_omegaH n hlam h
  · exact unscaledFullCoefficient_eq_angular_omegaL n hlam h

theorem scaledPhysicalCoefficient_summable_jet_majorant_upper
    {lam b : ℝ} {B S A zeta : ℂ → ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam 1 (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im) (hlam : 0<lam)
    (hphysical : ∀u∈U, zeta u∈(omegaH lam\{0})∪omegaL lam) (j : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∃ G : ℕ → ℝ, Summable G ∧
      ∀ w : ℂ, 0<w.im → ‖w‖<δ → w∈U → ∀ k : ℕ,
        ‖iteratedDeriv j (fun v => (A v)^(2*j+3+k+1)*
          FormFactors.unscaledFullCoefficient (2*j+3+k+1) lam (zeta v)) w‖≤G k := by
  obtain ⟨δ,hδ,G,hG,hbound⟩ := scaledPositiveCoefficient_summable_jet_majorant_upper
    hb hB0 hBa hSa hSzero hAa0 hA0 hU ha hAa hz hS0 hB hS he hup hBi j
  refine ⟨δ,hδ,G,hG,?_⟩
  intro w hw hwδ hwU k
  have heq : (fun v => (A v)^(2*j+3+k+1)*
      FormFactors.unscaledFullCoefficient (2*j+3+k+1) lam (zeta v)) =ᶠ[𝓝 w]
      (fun v => (A v)^(2*j+3+k+1)*unscaledAngularCoefficient (2*j+3+k) lam (zeta v)) := by
    filter_upwards [hU.mem_nhds hwU] with v hv
    rw [unscaledFullCoefficient_eq_angular_physical (2*j+3+k) hlam (hphysical v hv)]
  rw [heq.iteratedDeriv_eq j]
  exact hbound w hw hwδ hwU k

theorem physicalParity_tail_summable_jet_majorants_upper
    {lam b : ℝ} {B S A zeta : ℂ → ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam 1 (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im) (hlam : 0<lam)
    (hphysical : ∀u∈U, zeta u∈(omegaH lam\{0})∪omegaL lam) (hAsq : ∀u∈U, (A u)^2=spectralProduct lam (zeta u)) (j : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∃ Ghigh Glow : ℕ → ℝ, Summable Ghigh ∧ Summable Glow ∧
      ∀ w : ℂ, 0<w.im → ‖w‖<δ → w∈U → ∀ n : ℕ,
      ‖iteratedDeriv j (fun v => A v*(spectralProduct lam (zeta v))^(j+2+n)*
        FormFactors.unscaledFullCoefficient (2*(j+2+n)+1) lam (zeta v)) w‖≤Ghigh n ∧
      ‖iteratedDeriv j (fun v => (spectralProduct lam (zeta v))^(j+2+n)*
        FormFactors.unscaledFullCoefficient (2*(j+2+n)) lam (zeta v)) w‖≤Glow n := by
  obtain ⟨δ,hδ,G,hG,hbound⟩ := scaledPhysicalCoefficient_summable_jet_majorant_upper
    hb hB0 hBa hSa hSzero hAa0 hA0 hU ha hAa hz hS0 hB hS he hup hBi hlam hphysical j
  have hH : Summable (fun n : ℕ => G (2*n+1)) :=
    hG.comp_injective (by intro a b h; change 2*a+1=2*b+1 at h; omega)
  have hL : Summable (fun n : ℕ => G (2*n)) :=
    hG.comp_injective (by intro a b h; change 2*a=2*b at h; omega)
  refine ⟨δ,hδ,_,_,hH,hL,?_⟩
  intro w hw hwδ hwU n
  constructor
  · have heq : (fun v => A v*(spectralProduct lam (zeta v))^(j+2+n)*
        FormFactors.unscaledFullCoefficient (2*(j+2+n)+1) lam (zeta v)) =ᶠ[𝓝 w]
        (fun v => (A v)^(2*(j+2+n)+1)*
          FormFactors.unscaledFullCoefficient (2*(j+2+n)+1) lam (zeta v)) := by
      filter_upwards [hU.mem_nhds hwU] with v hv
      rw [←hAsq v hv,pow_add (A v) (2*(j+2+n)) 1,pow_one,pow_mul]
      ring
    rw [heq.iteratedDeriv_eq j,show 2*(j+2+n)+1=2*j+3+(2*n+1)+1 by omega]
    exact hbound w hw hwδ hwU (2*n+1)
  · have heq : (fun v => (spectralProduct lam (zeta v))^(j+2+n)*
        FormFactors.unscaledFullCoefficient (2*(j+2+n)) lam (zeta v)) =ᶠ[𝓝 w]
        (fun v => (A v)^(2*(j+2+n))*
          FormFactors.unscaledFullCoefficient (2*(j+2+n)) lam (zeta v)) := by
      filter_upwards [hU.mem_nhds hwU] with v hv
      rw [←hAsq v hv,pow_mul]
    rw [heq.iteratedDeriv_eq j,show 2*(j+2+n)=2*j+3+(2*n)+1 by omega]
    exact hbound w hw hwδ hwU (2*n)

end IsingBulk.Anisotropic.RegularEdges

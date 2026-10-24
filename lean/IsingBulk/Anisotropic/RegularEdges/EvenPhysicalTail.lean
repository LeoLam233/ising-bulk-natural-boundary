import IsingBulk.Anisotropic.RegularEdges.EvenScaledJets
import IsingBulk.Anisotropic.RegularEdges.ScaledPhysicalTail

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter MeasureTheory FormFactors
open scoped Topology

section Chart
variable {lam b : ℝ} {B S A zeta : ℂ→ℂ} {U : Set ℂ}
variable (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
  (hz : ∀u∈U,zeta u∉spectralSet lam) (hs : ∀u∈U,spectralS (zeta u)≠0)
  (hB : ∀u∈U,B u= -spectralT lam (zeta u)/spectralS (zeta u))
  (hS : ∀u∈U,S u=spectralS (zeta u))
  (he : ∀u∈U,edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
  (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im) (hlam : 0<lam)
  (hphysical : ∀u∈U,zeta u∈(omegaH lam\{0})∪omegaL lam)
include hU ha hz hs hB hS he hup hBi hlam hphysical

theorem unscaledPhysicalCoefficient_negative_fullJet_eq (n j : ℕ) (hn : Even (n+1)) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => unscaledFullCoefficient (n+1) lam (zeta v)) u=
      edgeCoefficientNormalization n*edgeFullDerivativeIntegral (n := n) b B (fun v => Complex.I*S v) j u := by
  have heq : (fun v => unscaledFullCoefficient (n+1) lam (zeta v))=ᶠ[𝓝 u]
      (fun v => unscaledAngularCoefficient n lam (zeta v)) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    exact unscaledFullCoefficient_eq_angular_physical n hlam (hphysical v hv)
  rw [heq.iteratedDeriv_eq j]
  exact unscaledAngularCoefficient_negative_fullJet_eq n j hn hU ha hz hs hB hS he hup hBi hu

theorem negativeEvenPhysical_tail_majorant_upper
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0) (hAa : AnalyticOnNhd ℂ A U)
    (hAsq : ∀u∈U,A u^2=spectralProduct lam (zeta u)) (j : ℕ) :
    ∃δ : ℝ,0<δ ∧ ∃G : ℕ→ℝ,Summable G ∧ ∀w : ℂ,0<w.im → ‖w‖<δ → w∈U → ∀k : ℕ,
      ‖iteratedDeriv j (fun v => (spectralProduct lam (zeta v))^(j+2+k)*
        unscaledFullCoefficient (2*(j+2+k)) lam (zeta v)) w‖≤G k := by
  obtain ⟨δ,r,C,M,D,hδ,hr,hr1,hC,hM,_,hbound⟩ := edgeFullIntegrand_integrated_jets_upper
    hb hB0 hBa ((analyticAt_const.mul hSa).div hAa0 hA0)
      (div_ne_zero (mul_ne_zero Complex.I_ne_zero hS0) hA0) j
  let G : ℕ→ℝ := fun k => D*particleEdgeMajorant r C M (2*j+3+2*k+1)*((2*j+3+2*k+1:ℕ):ℝ)^j
  have hsumm := particleEdgeMajorant_polynomial_summable hr hr1 hC hM j
  have hi : Function.Injective (fun k : ℕ => 2*j+3+2*k+1) := by intro a b h; dsimp at h; omega
  have hG : Summable G := by
    have hh := (hsumm.comp_injective hi).mul_left D
    convert hh using 1
    funext k
    dsimp [G,Function.comp_def]
    ring
  refine ⟨δ,hδ,G,hG,?_⟩
  intro w hw hwδ hwU k
  have hN : 2*j+3+2*k+1=2*(j+2+k) := by omega
  have hn : Even (2*j+3+2*k+1) := ⟨j+2+k,by omega⟩
  have heq : (fun v => (spectralProduct lam (zeta v))^(j+2+k)*
      unscaledFullCoefficient (2*(j+2+k)) lam (zeta v))=ᶠ[𝓝 w]
      (fun v => (A v)^(2*j+3+2*k+1)*unscaledAngularCoefficient (2*j+3+2*k) lam (zeta v)) := by
    filter_upwards [hU.mem_nhds hwU] with v hv
    rw [←hN,unscaledFullCoefficient_eq_angular_physical (2*j+3+2*k) hlam (hphysical v hv),
      hN,pow_mul,hAsq v hv]
  rw [heq.iteratedDeriv_eq j,scaledNegativeEvenCoefficient_iteratedDeriv (2*j+3+2*k) j hn
    hU ha hAa hz hs hB hS he hup hBi hwU,norm_mul]
  have hf : ‖(((2*j+3+2*k+1).factorial:ℂ)⁻¹)‖≤1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (2*j+3+2*k+1)))
  exact (mul_le_of_le_one_left (norm_nonneg _) hf).trans (hbound w hw hwδ (2*k))

end Chart
end
end IsingBulk.Anisotropic.RegularEdges

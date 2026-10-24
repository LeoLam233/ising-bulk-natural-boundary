import IsingBulk.Anisotropic.NegativeCycles.ModelTailRatio
import IsingBulk.Anisotropic.NegativeCycles.ModelPeriodNorm
import IsingBulk.Anisotropic.NegativeNormalForm.ComplexPeriodLoss

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First

 theorem central_model_cutoff_ratio_small {N : ℕ} (hN : 0<N) (h : ℂ)
    (hh : (1:ℝ)/2≤h.re) (σ : ℝ) (hσ : 0<σ) (hlarge : 32*Real.pi^2≤(N:ℝ)*σ) :
    tau N/(tau N+(h/(2*(N:ℂ))).re*σ)≤1/16 := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have ht := tau_pos N hN
  have hscale := (scaled_tau_bounds N hN).2
  have hlinear : 64*(N:ℝ)*tau N≤σ := by
    nlinarith
  have hprod : 32*(N:ℝ)*tau N≤h.re*σ := by nlinarith
  have hden : 16*tau N≤h.re/(2*(N:ℝ))*σ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0<2*(N:ℝ))).mpr
    nlinarith
  have hre : (h/(2*(N:ℂ))).re=h.re/(2*(N:ℝ)) := by
    convert Complex.div_ofReal_re h (2*(N:ℝ)) using 1; push_cast; rfl
  rw [hre]
  apply (div_le_iff₀ (show 0<tau N+h.re/(2*(N:ℝ))*σ by positivity)).mpr
  linarith

/-- Removed fixed-cutoff model tail is geometrically small, relative to the genuine
complex period; the exact complex normalization loss is retained. -/
theorem physical_model_cutoff_tail {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : 2*alpha (n+1)≤j) (h : ℂ) (hh : (1:ℝ)/2≤h.re)
    (b : ContDiffBump (0:ℝ)) (hlarge : 32*Real.pi^2≤(n+1:ℕ)*b.rIn) :
    ‖∫q : Fin n→ℝ,(1-(shapeSpatialCutoff b q:ℂ))*
      quadraticModelKernel n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ)) q‖≤
      ((1/2:ℝ)^j*(‖h‖/h.re)^(alpha (n+1)))*
        ‖shapePeriod n j (tau (n+1)) (h/(2*(n+1:ℕ):ℂ))‖ := by
  have hNr : (0:ℝ)<(n+1:ℕ) := by positivity
  have hτ := tau_pos (n+1) (by omega)
  have hre : (h/(2*(n+1:ℕ):ℂ)).re=h.re/(2*(n+1:ℕ):ℝ) := by
    convert Complex.div_ofReal_re h (2*(n+1:ℕ):ℝ) using 1; push_cast; rfl
  have hc : 0<(h/(2*(n+1:ℕ):ℂ)).re := by rw [hre]; positivity
  have hs := central_model_cutoff_ratio_small (show 0<n+1 by omega) h hh b.rIn b.rIn_pos hlarge
  have he := model_cutoff_geometric_bound ho hn j hj (tau (n+1)) hτ
    (h/(2*(n+1:ℕ):ℂ)) hc b hs
  rw [betaValue_eq_complex_period_norm ho hn j (by omega) (tau (n+1)) hτ _ hc] at he
  have hratio : ‖h/(2*(n+1:ℕ):ℂ)‖/(h/(2*(n+1:ℕ):ℂ)).re=‖h‖/h.re := by
    rw [hre,norm_div]
    have hnorm : ‖(2*(n+1:ℕ):ℂ)‖=(2*(n+1:ℕ):ℝ) := by
      rw [norm_mul,Complex.norm_ofNat,Complex.norm_natCast]
    rw [hnorm]
    field_simp
  rw [hratio] at he
  simpa only [mul_assoc] using he

end IsingBulk.Anisotropic.NegativeCycles

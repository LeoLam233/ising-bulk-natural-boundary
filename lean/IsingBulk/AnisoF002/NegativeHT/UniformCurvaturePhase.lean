import IsingBulk.AnisoF002.NegativeHT.ComplexPeriodPhase

/-!
# Uniform phase control at the actual first-winding centers

The explicit curvature from F002 `eq:rc-h` is used throughout.  A bound
on the analytic anisotropy factor B at the centers gives a concrete
large-n threshold and the full `exp(C / n^2)` comparison in
`eq:rc-phase-cost`, including the previously stored exact scalar model.
No relation between that scalar model and the physical pole density is
assumed or claimed here.
-/

namespace IsingBulk.AnisoF002.NegativeHT

noncomputable section

/-- A small full complex curvature error gives a quadratic phase cost.
The imaginary part is squared before multiplying by the particle exponent. -/
theorem curvature_phase_cost_of_close (α : ℕ) {h : ℂ} {δ : ℝ}
    (hd : δ ≤ 1/2) (hh : ‖h-1‖ ≤ δ) :
    0 < h.re ∧ 1 ≤ (‖h‖/h.re)^α ∧
      (‖h‖/h.re)^α ≤ Real.exp (2*(α : ℝ)*δ^2) := by
  have hre : |h.re-1| ≤ δ := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (Complex.abs_re_le_norm (h-1)).trans hh
  have him : |h.im| ≤ δ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using
      (Complex.abs_im_le_norm (h-1)).trans hh
  have hr : (1:ℝ)/2 ≤ h.re := by
    have hp := (abs_le.mp hre).1
    linarith
  have hr0 : 0 < h.re := by linarith
  have hi2 : h.im^2 ≤ δ^2 := by
    have hp := (abs_le.mp him).1
    have hq := (abs_le.mp him).2
    nlinarith
  have hr2 : (1:ℝ)/4 ≤ h.re^2 := by nlinarith
  have he : (α : ℝ)*h.im^2/(2*h.re^2) ≤ 2*(α : ℝ)*δ^2 := by
    calc
      _ ≤ (α : ℝ)*δ^2/(2*h.re^2) := by gcongr
      _ ≤ (α : ℝ)*δ^2/(2*((1:ℝ)/4)) := by gcongr
      _ = _ := by ring
  have hc := curvature_phase_cost α hr0
  exact ⟨hr0, hc.1, hc.2.trans (Real.exp_le_exp.mpr he)⟩

/-- The explicit n-independent constant in the actual curvature error. -/
def curvatureErrorConstant (K b s : ℝ) : ℝ :=
  (1+2*K*|b|/s^2)*Real.pi^2/2

/-- Quantitative uniform form of the paper's phase estimate.  The sole
large-n condition is explicit, rather than hidden in big-O notation. -/
theorem firstWindingCurvature_phase_uniform (n α : ℕ) (B : ℂ) (b s K : ℝ)
    (hn : 0<n) (hα : α≤n^2) (hK : ‖B‖≤K)
    (hlarge : 2*curvatureErrorConstant K b s ≤ (n : ℝ)^2) :
    0 < (firstWindingCurvature n B b s).re ∧
      1 ≤ (‖firstWindingCurvature n B b s‖ /
        (firstWindingCurvature n B b s).re)^α ∧
      (‖firstWindingCurvature n B b s‖ /
        (firstWindingCurvature n B b s).re)^α ≤
        Real.exp (2*(curvatureErrorConstant K b s)^2/(n : ℝ)^2) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hK0 : 0≤K := (norm_nonneg _).trans hK
  have hC : 0 ≤ curvatureErrorConstant K b s := by
    unfold curvatureErrorConstant
    positivity
  have he := firstWindingCurvature_uniform_bound n B b s K hn hK
  have he' : ‖firstWindingCurvature n B b s-1‖ ≤
      curvatureErrorConstant K b s/(n : ℝ)^2 := by
    convert he using 1
    unfold curvatureErrorConstant
    ring
  have hd : curvatureErrorConstant K b s/(n : ℝ)^2 ≤ 1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    linarith
  have hc := curvature_phase_cost_of_close α hd he'
  have hα' : (α : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast hα
  have hexp : 2*(α : ℝ)*(curvatureErrorConstant K b s/(n : ℝ)^2)^2 ≤
      2*(curvatureErrorConstant K b s)^2/(n : ℝ)^2 := by
    calc
      _ ≤ 2*(n : ℝ)^2*(curvatureErrorConstant K b s/(n : ℝ)^2)^2 := by gcongr
      _ = _ := by field_simp
  exact ⟨hc.1, hc.2.1, hc.2.2.trans (Real.exp_le_exp.mpr hexp)⟩

/-- The exact particle exponent obeys the uniform bound needed above. -/
theorem particleExponent_le_sq (n : ℕ) : particleExponent n ≤ n^2 := by
  unfold particleExponent
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

/-- Full exact-model phase comparison at the physical first-winding
curvature and pole-center scale.  All model factors remain present. -/
theorem firstWindingModel_phase_uniform (n j : ℕ) (B : ℂ) (b s K : ℝ)
    (hn : 0<n) (hs : 0<s) (hK : ‖B‖≤K)
    (hlarge : 2*curvatureErrorConstant K b s ≤ (n : ℝ)^2) :
    ‖modelCoefficient n j B (firstWindingCurvature n B b s) s (windingTau n)‖ ≤
      ‖modelCoefficient n j B
        ((firstWindingCurvature n B b s).re : ℂ) s (windingTau n)‖ ∧
    ‖modelCoefficient n j B
        ((firstWindingCurvature n B b s).re : ℂ) s (windingTau n)‖ ≤
      Real.exp (2*(curvatureErrorConstant K b s)^2/(n : ℝ)^2) *
        ‖modelCoefficient n j B (firstWindingCurvature n B b s) s (windingTau n)‖ := by
  have hc := firstWindingCurvature_phase_uniform n (particleExponent n)
    B b s K hn (particleExponent_le_sq n) hK hlarge
  rw [norm_modelCoefficient_realPart_curvature n j B s (windingTau n)
    hn hs (windingTau_pos n hn) hc.1]
  constructor
  · simpa using mul_le_mul_of_nonneg_right hc.2.1
      (norm_nonneg (modelCoefficient n j B (firstWindingCurvature n B b s) s (windingTau n)))
  · exact mul_le_mul_of_nonneg_right hc.2.2
      (norm_nonneg (modelCoefficient n j B (firstWindingCurvature n B b s) s (windingTau n)))

end

end IsingBulk.AnisoF002.NegativeHT

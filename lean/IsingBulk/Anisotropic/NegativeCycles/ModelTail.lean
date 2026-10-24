import IsingBulk.Anisotropic.NegativeDominance.ConstrainedBetaKernel
import IsingBulk.Anisotropic.NegativeCycles.CutoffGradient
import Mathlib.Data.Nat.Choose.Cast

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory

 def quadraticModelKernel (n j : ℕ) (τ : ℝ) (c : ℂ) (q : Fin n→ℝ) : ℂ :=
    (firstVandermonde (shapeExtend q):ℂ)^2/((τ:ℂ)+c*(constrainedSquaredRadius q:ℂ))^(j+1)

 theorem quadraticModelKernel_integral (n j : ℕ) (τ : ℝ) (c : ℂ) :
    (∫q,quadraticModelKernel n j τ c q)=shapePeriod n j τ c := by
  rw [shapePeriod_eq_sourceIntegral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  simp only [quadraticModelKernel,constrainedSquaredRadius_eq,squaredRadius,
    Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_pow]

 theorem quadraticModelKernel_tail_pointwise {n a j : ℕ} (haj : a≤j)
    (τ : ℝ) (hτ : 0<τ) (c : ℂ) (hc : 0<c.re) (σ : ℝ) (hσ : 0≤σ)
    (q : Fin n→ℝ) (hq : σ≤constrainedSquaredRadius q) :
    ‖quadraticModelKernel n j τ c q‖≤
      (τ+c.re*σ)⁻¹^(j-a)*constrainedBetaKernel n a τ c.re q := by
  let Q := constrainedSquaredRadius q
  let D := (τ:ℂ)+c*(Q:ℂ)
  have hQ : 0≤Q := constrainedSquaredRadius_nonneg q
  have hbase : 0<τ+c.re*Q := by positivity
  have hcut : 0<τ+c.re*σ := by positivity
  have hD : τ+c.re*Q≤‖D‖ := by
    have hh := Complex.re_le_norm D
    simpa only [D,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] using hh
  have hDC : τ+c.re*σ≤‖D‖ := by
    have hh := mul_le_mul_of_nonneg_left hq hc.le
    linarith
  have hpow : (τ+c.re*Q)^(a+1)*(τ+c.re*σ)^(j-a)≤‖D‖^(j+1) := by
    have hh := mul_le_mul (pow_le_pow_left₀ hbase.le hD (a+1))
      (pow_le_pow_left₀ hcut.le hDC (j-a)) (by positivity) (by positivity)
    rw [←pow_add,show a+1+(j-a)=j+1 by omega] at hh
    exact hh
  have hV : 0≤firstVandermonde (shapeExtend q)^2 := sq_nonneg _
  have hn : ‖quadraticModelKernel n j τ c q‖=
      firstVandermonde (shapeExtend q)^2/‖D‖^(j+1) := by
    simp only [quadraticModelKernel,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,_root_.sq_abs]
    rfl
  rw [hn]
  have hb := div_le_div_of_nonneg_left hV (show 0<(τ+c.re*Q)^(a+1)*(τ+c.re*σ)^(j-a) by positivity) hpow
  apply hb.trans_eq
  change _=(τ+c.re*σ)⁻¹^(j-a)*(firstVandermonde (shapeExtend q)^2/(τ+c.re*Q)^(a+1))
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

 theorem quadraticModel_cutoff_tail_bound {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (τ : ℝ) (hτ : 0<τ) (c : ℂ) (hc : 0<c.re)
    (b : ContDiffBump (0:ℝ)) :
    ‖∫q : Fin n→ℝ,(1-(shapeSpatialCutoff b q:ℂ))*quadraticModelKernel n j τ c q‖≤
      (τ+c.re*b.rIn)⁻¹^(j-alpha (n+1))*constrainedBetaValue (n+1) (alpha (n+1)) τ c.re := by
  let K := (τ+c.re*b.rIn)⁻¹^(j-alpha (n+1))
  have hK : 0≤K := by have := b.rIn_pos; dsimp [K]; positivity
  have hi := (constrainedBetaKernel_integrable ho hn (alpha (n+1)) le_rfl τ c.re hτ hc).const_mul K
  have hbnd (q : Fin n→ℝ) :
      ‖(1-(shapeSpatialCutoff b q:ℂ))*quadraticModelKernel n j τ c q‖≤
        K*constrainedBetaKernel n (alpha (n+1)) τ c.re q := by
    by_cases hq : constrainedSquaredRadius q≤b.rIn
    · rw [shapeSpatialCutoff_one b hq]
      simp only [Complex.ofReal_one,sub_self,zero_mul,norm_zero]
      exact mul_nonneg hK (constrainedBetaKernel_nonneg _ _ hτ.le hc.le q)
    · have hh := quadraticModelKernel_tail_pointwise hj τ hτ c hc b.rIn b.rIn_pos.le q (le_of_not_ge hq)
      have hcut : ‖1-(shapeSpatialCutoff b q:ℂ)‖≤1 := by
        rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        have h0 : 0≤shapeSpatialCutoff b q := b.nonneg
        have h1 : shapeSpatialCutoff b q≤1 := b.le_one
        rw [abs_of_nonneg (by linarith)]
        linarith
      rw [norm_mul]
      exact (mul_le_mul hcut hh (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbnd)
  rw [integral_const_mul,constrainedBetaKernel_integral ho hn _ le_rfl τ c.re hτ hc] at hh
  exact hh

end IsingBulk.Anisotropic.NegativeCycles

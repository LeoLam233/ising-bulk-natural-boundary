import IsingBulk.First.PeriodicYSupport

/-! Separation of the two actual y-chart supports and vanishing of the
remaining fixed complement near each bad configuration. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter Metric
open scoped Topology ContDiff BigOperators

theorem angularChartVector_center {N : ℕ} (alpha : ℝ) {theta : Fin N → ℝ}
    (hc : ∀ j, exp (((theta j+alpha:ℝ):ℂ)*I) = 1) : angularChartVector alpha theta = 0 := by
  funext j
  simp only [angularChartVector,periodicAngle,hc j,Complex.log_one,Complex.zero_im,Pi.zero_apply]

theorem fixedYChartWeight_eventually_one {n : ℕ} (alpha : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ}
    (hchi : chi =ᶠ[𝓝 0] (fun _ => 1)) (heta : eta =ᶠ[𝓝 0] (fun _ => 1))
    {theta : Fin (n+1) → ℝ} (hc : ∀ j, exp (((theta j+alpha:ℝ):ℂ)*I) = 1) :
    fixedYChartWeight alpha chi eta =ᶠ[𝓝 theta] (fun _ => 1) := by
  have hcos (j : Fin (n+1)) : Real.cos (theta j+alpha) = 1 := by
    have h := congrArg Complex.re (hc j)
    simpa only [Complex.exp_ofReal_mul_I_re,Complex.one_re] using h
  have hu (j : Fin (n+1)) : ContinuousAt
      (fun t : Fin (n+1) → ℝ => periodicAngle (t j+alpha)) theta :=
    (ContDiffAt.comp (f := fun t : Fin (n+1) → ℝ => t j+alpha) (g := periodicAngle)
      theta (periodicAngle_contDiffAt (by rw [hcos]; norm_num)) (by fun_prop)).continuousAt
  have hm : ContinuousAt (fun t : Fin (n+1) → ℝ => meanCoordinate (angularChartVector alpha t)) theta := by
    unfold meanCoordinate angularChartVector
    fun_prop
  have hs : ContinuousAt (fun t : Fin (n+1) → ℝ =>
      fun j : Fin n => shapeCoordinates (angularChartVector alpha t) j.castSucc) theta := by
    unfold shapeCoordinates angularChartVector
    fun_prop
  have hzero := angularChartVector_center alpha hc
  have hmean : meanCoordinate (angularChartVector alpha theta) = 0 := by simp [hzero,meanCoordinate]
  have hshape : (fun j : Fin n => shapeCoordinates (angularChartVector alpha theta) j.castSucc) = 0 := by
    funext j
    simp [hzero,shapeCoordinates,meanCoordinate]
  have hmt := hm.tendsto
  have hst := hs.tendsto
  rw [hmean] at hmt
  rw [hshape] at hst
  have hg : ∀ᶠ t : Fin (n+1) → ℝ in 𝓝 theta, angularChartGate alpha t = 1 := by
    have hbounds : ∀ᶠ t : Fin (n+1) → ℝ in 𝓝 theta, ∀ j, 3/4 ≤ Real.cos (t j+alpha) := by
      apply Filter.eventually_all.mpr
      intro j
      have hh : ContinuousAt (fun t : Fin (n+1) → ℝ => Real.cos (t j+alpha)) theta :=
        (Real.continuous_cos.comp ((continuous_apply j).add continuous_const)).continuousAt
      exact hh.eventually (Ici_mem_nhds (by change 3/4 < Real.cos (theta j+alpha); rw [hcos]; norm_num))
    filter_upwards [hbounds] with t ht
    exact Finset.prod_eq_one (fun j _ => angularGate_eq_one (ht j))
  filter_upwards [hchi.comp_tendsto hst,heta.comp_tendsto hmt,hg] with t ht he hg
  simp only [Function.comp_apply] at ht he
  simp only [fixedYChartWeight,hg,ht,he,one_mul]

theorem fixedYChartWeight_disjoint {n : ℕ} (alpha beta : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ} {H delta : ℝ}
    (hsmall : H+delta ≤ 1)
    (hsep : 4*(H+delta) ≤ ‖exp (-(alpha:ℂ)*I)-exp (-(beta:ℂ)*I)‖)
    (hchi : ∀ t, chi t ≠ 0 → ∀ j, |shapeExtend t j| < H)
    (heta : ∀ v, eta v ≠ 0 → |v| < delta)
    (theta : Fin (n+1) → ℝ) :
    fixedYChartWeight alpha chi eta theta ≠ 0 → fixedYChartWeight beta chi eta theta = 0 := by
  intro ha
  by_contra hb
  have hA := fixedYChartWeight_support_circle alpha hsmall hchi heta ha (0 : Fin (n+1))
  have hB := fixedYChartWeight_support_circle beta hsmall hchi heta hb (0 : Fin (n+1))
  have ht := norm_sub_le_norm_sub_add_norm_sub (exp (-(alpha:ℂ)*I))
    (exp ((theta 0:ℂ)*I)) (exp (-(beta:ℂ)*I))
  rw [norm_sub_rev (exp (-(alpha:ℂ)*I)) (exp ((theta 0:ℂ)*I))] at ht
  linarith

def fixedYComplement {n : ℕ} (alpha beta : ℝ) (chi : (Fin n → ℝ) → ℝ) (eta : ℝ → ℝ)
    (theta : Fin (n+1) → ℝ) : ℝ :=
  1-fixedYChartWeight alpha chi eta theta-fixedYChartWeight beta chi eta theta

theorem fixedYComplement_contDiff {n : ℕ} (alpha beta : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ chi) (he : ContDiff ℝ ∞ eta) :
    ContDiff ℝ ∞ (fixedYComplement alpha beta chi eta) :=
  (contDiff_const.sub (fixedYChartWeight_contDiff alpha hc he)).sub
    (fixedYChartWeight_contDiff beta hc he)

theorem fixedYComplement_excludes_center {n : ℕ} (alpha beta : ℝ)
    {chi : (Fin n → ℝ) → ℝ} {eta : ℝ → ℝ}
    (hchi : chi =ᶠ[𝓝 0] (fun _ => 1)) (heta : eta =ᶠ[𝓝 0] (fun _ => 1))
    (hdisj : ∀ t, fixedYChartWeight alpha chi eta t ≠ 0 → fixedYChartWeight beta chi eta t = 0)
    {theta : Fin (n+1) → ℝ} (hc : ∀ j, exp (((theta j+alpha:ℝ):ℂ)*I) = 1) :
    theta ∉ tsupport (fixedYComplement alpha beta chi eta) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [fixedYChartWeight_eventually_one alpha hchi heta hc] with t ht
  have hv := hdisj t (by rw [ht]; norm_num)
  simp [fixedYComplement,ht,hv]

end
end IsingBulk.First

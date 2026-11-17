import Mathlib.Analysis.Complex.Liouville
import IsingBulk.AnisoF002.C03.RegularProtectedMatching
import IsingBulk.AnisoF002.C03.RegularIsotropicContinuedDensity

/-!
# Complete physical mixed-density bounds and every parameter jet

The literal normalization, signed product kernel, all one-body and pair
factors are retained on the constructed disk. Cauchy bounds transfer to
the original physical germ, with a polynomial N^(6j) derivative cost.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

def mixedDensityEnvelope (C g : ℝ) (N : ℕ) : ℝ :=
  ‖isotropicParticleNormalization N‖ * ((4 / g) * N) * 4 ^ N *
    (matchingNumber ((N + 1) / 2) : ℝ) * (16 * C) ^ N * Real.exp 1 * Real.exp ((N : ℝ) / 2)

def actualBodyNormProduct {N : ℕ} (S : ℂ) (η τ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  ∏ i, ‖2 * isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) /
    (1 - isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) ^ 2)‖

theorem product_kernel_norm_of_norm_gap {p σ : ℂ} {h : ℝ} (hh : 0 < h)
    (hσ : ‖σ‖ ≤ 1) (hgap : ‖p‖ ≤ 1 - h) :
    1 - σ * p ≠ 0 ∧ ‖(1 + σ * p) / (1 - σ * p)‖ ≤ 2 / h := by
  have hsp : ‖σ * p‖ ≤ ‖p‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ (norm_nonneg p)
  have hd : h ≤ ‖1 - σ * p‖ := by
    have he := norm_sub_norm_le (1 : ℂ) (σ * p)
    rw [norm_one] at he
    linarith
  have hdz : 1 - σ * p ≠ 0 := norm_pos_iff.mp (hh.trans_le hd)
  refine ⟨hdz, ?_⟩
  have hn : ‖1 + σ * p‖ ≤ 2 := by
    have he := norm_add_le (1 : ℂ) (σ * p)
    rw [norm_one] at he
    linarith
  rw [norm_div]
  exact div_le_div₀ (by norm_num) hn hh hd

namespace ActualMixedRootControl
variable {α b η τ δ : ℝ} (d : ActualMixedRootControl α b η τ δ)

theorem continued_kernel_bound {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    {σ z : ℂ} (hσ : ‖σ‖ ≤ 1) (hz : ‖z‖ ≤ d.radius / (N : ℝ) ^ 6) :
    1 - σ * ∏ i, mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i ≠ 0 ∧
      ‖(1 + σ * ∏ i, mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i) /
        (1 - σ * ∏ i, mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i)‖ ≤
      (4 / d.productGap) * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := product_kernel_norm_of_norm_gap
    (by positivity [d.productGap_pos] : 0 < d.productGap / (2 * N)) hσ
    (d.disk_bounds N hN ε hε hεδ θ hP hQ z hz).2.2.2.2
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  field_simp
  ring

theorem continued_body_bound {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    {z : ℂ} (hz : ‖z‖ ≤ d.radius / (N : ℝ) ^ 6) (i : Fin N) :
    ‖2 * mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i /
      (1 - mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i ^ 2)‖ ≤
      4 * ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) /
        (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, actualHomotopyAngle η τ 1 θ i) ^ 2)‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨_, hR, hhalf, _, _⟩ := d.disk_bounds N hN ε hε hεδ θ hP hQ z hz
  apply oneBody_relative_bound (hR i)
  · simpa only [pow_two] using hhalf i i
  · apply norm_pos_iff.mp
    have hg := d.center_gap N hN ε hε hεδ θ hP hQ i i
    simpa only [pow_two] using (div_pos d.pairGap_pos hN0).trans_le hg

theorem continued_density_analytic {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    {σ z : ℂ} (hσ : ‖σ‖ ≤ 1) (hz : ‖z‖ ≤ d.radius / (N : ℝ) ^ 6) :
    AnalyticAt ℂ (mixedContinuedDensity (isotropicRadialParameter α ε) σ η τ θ) z := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hr, _, hh, _, _⟩ := d.disk_bounds N hN ε hε hεδ θ hP hQ z hz
  let R := mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ
  have hd (i j : Fin N) : 1 - R z i * R z j ≠ 0 := by
    apply norm_pos_iff.mp
    apply lt_of_lt_of_le _ (hh i j)
    exact half_pos ((div_pos d.pairGap_pos hN0).trans_le (d.center_gap N hN ε hε hεδ θ hP hQ i j))
  have hprod : AnalyticAt ℂ (fun t => ∏ i, R t i) z :=
    Finset.analyticAt_fun_prod _ (fun i _ => hr i)
  have hbody (i : Fin N) : AnalyticAt ℂ (fun t => 2 * R t i / (1 - R t i ^ 2)) z :=
    (analyticAt_const.mul (hr i)).div (analyticAt_const.sub ((hr i).pow 2))
      (by simpa only [pow_two] using hd i i)
  have hpair (ij : Fin N × Fin N) : AnalyticAt ℂ (fun t => canceledPair 1 (R t ij.1) (R t ij.2)
      (Complex.exp (actualHomotopyAngle η τ 1 θ ij.1 * Complex.I))
      (Complex.exp (actualHomotopyAngle η τ 1 θ ij.2 * Complex.I))) z := by
    unfold canceledPair
    apply ((analyticAt_const.mul (hr ij.1)).mul (hr ij.2)).div
      (analyticAt_const.mul ((analyticAt_const.sub ((hr ij.1).mul (hr ij.2))).pow 2))
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
      (pow_ne_zero _ (hd ij.1 ij.2))
  unfold mixedContinuedDensity
  exact ((analyticAt_const.mul
    ((analyticAt_const.add (analyticAt_const.mul hprod)).div
      (analyticAt_const.sub (analyticAt_const.mul hprod))
      (d.continued_kernel_bound hN hε hεδ θ hP hQ hσ hz).1)).mul
      (Finset.analyticAt_fun_prod _ (fun i _ => hbody i))).mul
        (Finset.analyticAt_fun_prod _ (fun ij _ => hpair ij))

theorem continued_density_bound {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    {σ z : ℂ} (hσ : ‖σ‖ ≤ 1) (hz : ‖z‖ ≤ d.radius / (N : ℝ) ^ 6) :
    ‖mixedContinuedDensity (isotropicRadialParameter α ε) σ η τ θ z‖ ≤
      mixedDensityEnvelope d.pairConstant d.productGap N *
        actualBodyNormProduct (isotropicRadialParameter α ε) η τ θ := by
  have hb : (∏ i, ‖2 * mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i /
        (1 - mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i ^ 2)‖) ≤
      4 ^ N * actualBodyNormProduct (isotropicRadialParameter α ε) η τ θ := by
    have hh := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => norm_nonneg _)
      (fun i (_ : i ∈ Finset.univ) => d.continued_body_bound hN hε hεδ θ hP hQ hz i)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      actualBodyNormProduct] using hh
  unfold mixedContinuedDensity
  rw [norm_mul, norm_mul, norm_mul, norm_prod]
  have hk := (d.continued_kernel_bound hN hε hεδ θ hP hQ hσ hz).2
  have hp := d.continued_pair_bound hN hε hεδ θ hP hQ hz
  have hbody0 : 0 ≤ actualBodyNormProduct (isotropicRadialParameter α ε) η τ θ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hnewbody0 : 0 ≤ ∏ i, ‖2 * mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i /
      (1 - mixedContinuedRoots (isotropicRadialParameter α ε) η τ θ z i ^ 2)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hk0 : 0 ≤ (4 / d.productGap) * (N : ℝ) := by positivity [d.productGap_pos]
  have h1 := mul_le_mul_of_nonneg_left hk (norm_nonneg (isotropicParticleNormalization N))
  have h2 := mul_le_mul h1 hb hnewbody0
    (mul_nonneg (norm_nonneg (isotropicParticleNormalization N)) hk0)
  have h3 := mul_le_mul h2 hp (norm_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg (isotropicParticleNormalization N)) hk0)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) N) hbody0))
  apply h3.trans_eq
  unfold mixedDensityEnvelope
  ring

theorem physical_density_jet_bound {N : ℕ} (hN : 0 < N)
    (hα : 0 < α ∧ α < Real.pi) (hδ1 : δ ≤ 1) (hη : 0 < η) (hτ : 0 ≤ τ)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ) (hQ : 1 / 4 ≤ actualLowerPopulation η θ)
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (j : ℕ) :
    ‖iteratedDeriv j (fun z => isotropicBarePhysicalDensity (isotropicRadialParameter α ε + z) σ
        (actualHomotopyAngle η τ 1 θ)) 0‖ ≤
      ((j.factorial : ℝ) * mixedDensityEnvelope d.pairConstant d.productGap N /
        (d.radius / (N : ℝ) ^ 6) ^ j) *
      actualBodyNormProduct (isotropicRadialParameter α ε) η τ θ := by
  rw [← mixedContinuedDensity_physical_jets _ σ
    (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1 η τ hη hτ θ j]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 0 < d.radius / (N : ℝ) ^ 6 := by positivity [d.radius_pos]
  calc
    _ ≤ (j.factorial : ℝ) * (mixedDensityEnvelope d.pairConstant d.productGap N *
        actualBodyNormProduct (isotropicRadialParameter α ε) η τ θ) /
        (d.radius / (N : ℝ) ^ 6) ^ j := by
      apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
      · apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ (ne_of_gt hR)]
        intro z hz
        exact (d.continued_density_analytic hN hε hεδ θ hP hQ hσ
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).differentiableAt.differentiableWithinAt
      · intro z hz
        apply d.continued_density_bound hN hε hεδ θ hP hQ hσ
        have hc := Metric.sphere_subset_closedBall hz
        simpa only [Metric.mem_closedBall, dist_zero_right] using hc
    _ = _ := by ring

end ActualMixedRootControl
end
end IsingBulk.AnisoF002.Isotropic

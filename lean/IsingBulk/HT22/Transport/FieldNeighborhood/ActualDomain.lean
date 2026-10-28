import IsingBulk.HT22.Transport.FieldNeighborhood.OriginalJetInputs

/-! # Source-field jets from one fixed convex inverse domain

All assumptions are original inverse geometry: a genuine analytic branch,
its bounded first partial jets, base inverse differences, and the protected
mixed covariance. The conclusion is the actual F001 residual field jet.
-/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry
set_option backward.isDefEq.respectTransparency false

theorem sourceResidual_joint_jets_of_convex_inverse_domain {N : ℕ} (hN : 0<N)
    (x : SourcePoint N) (D : Set ℂ) (C H d c η : ℝ)
    (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c) (hdH : d≤H)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*(9*C)^2))
    (hD : Convex ℝ D)
    (hinside : ∀ i, closedBall (x.2 i) (η*d/(N:ℝ)^2) ⊆ D)
    (hU : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hVjet : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,q)‖≤C)
    (hTjet : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2) (t,q)‖≤C)
    (hT : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D → ‖sourceInverseT t q‖≤C)
    (hV0 : ∀ i, ‖sourceInverseV x.1 (x.2 i)‖≤C*H)
    (hdiam : ∀ i j, ‖x.2 i-x.2 j‖≤d)
    (hD0 : ∀ i j, ‖sourceInverseCoordinate i x-sourceInverseCoordinate j x‖≤C*H*d)
    (hE0 : ∀ i j, ‖sourceInverseVCoordinate i x-sourceInverseVCoordinate j x‖≤C*d)
    (hR0 : c*H*d^2≤‖sourceCovariance x.1 x.2‖) (m : ℕ) :
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceResidual z.1 z.2) x‖≤
      (IsingBulk.Preferred22.cauchyJetConstant m*(324*C^2/c)/η^m)*
        (N:ℝ)^(2*m+2)/d^(m+1) := by
  let ρ := η*d/(N:ℝ)^2
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρd : ρ≤d := by
    calc
      _ ≤ η*d := div_le_self (by positivity) (one_le_pow₀ hn1)
      _ ≤ d := mul_le_of_le_one_left hd.le hη1
  have htime (y : SourcePoint N) (hy : y∈closedBall x ρ) : ‖y.1-x.1‖≤ρ := by
    have h := norm_fst_le (y-x)
    exact h.trans (by simpa only [mem_closedBall, dist_eq_norm] using hy)
  have hcoord (y : SourcePoint N) (hy : y∈closedBall x ρ) (i : Fin N) :
      ‖y.2 i-x.2 i‖≤ρ := by
    have h := (norm_le_pi_norm (y.2-x.2) i).trans (norm_snd_le (y-x))
    exact h.trans (by simpa only [mem_closedBall, dist_eq_norm] using hy)
  have hmem (y : SourcePoint N) (hy : y∈closedBall x ρ) (i : Fin N) : y.2 i∈D :=
    hinside i (by simpa only [mem_closedBall, dist_eq_norm] using hcoord y hy i)
  have hUa (y : SourcePoint N) (hy : y∈closedBall x ρ) (i : Fin N) :=
    hU y.1 (y.2 i) (htime y hy) (hmem y hy i)
  have hVJa (y : SourcePoint N) (hy : y∈closedBall x ρ) (i : Fin N) :=
    hVjet y.1 (y.2 i) (htime y hy) (hmem y hy i)
  have hVa (y : SourcePoint N) (hy : y∈closedBall x ρ) (i : Fin N) :
      ‖sourceInverseV y.1 (y.2 i)‖≤(3*C)*H := by
    have hsmall := sourceInverseV_small_on_ball x y i ρ C H hρ.le (hρd.trans hdH)
      hC.le hy (fun z hz => hUa z hz i) (fun z hz => hVJa z hz i) (hV0 i)
    exact hsmall.trans (by nlinarith [mul_nonneg hC.le hH.le])
  have hTa (y : SourcePoint N) (hy : y∈closedBall x ρ) (i j : Fin N) :
      ‖sourceInverseT y.1 (y.2 i)-sourceInverseT y.1 (y.2 j)‖≤(3*C)*d := by
    have hpair := inverseT_pair_lipschitz y.1 (y.2 j) (y.2 i) D C hD
      (hmem y hy j) (hmem y hy i)
      (fun q hq => hU y.1 q (htime y hy) hq)
      (fun q hq => hTjet y.1 q (htime y hy) hq)
    have hdist : ‖y.2 i-y.2 j‖≤3*d := by
      have he : y.2 i-y.2 j = (y.2 i-x.2 i)+(x.2 i-x.2 j)-(y.2 j-x.2 j) := by ring
      rw [he]
      have hh := (norm_sub_le ((y.2 i-x.2 i)+(x.2 i-x.2 j)) (y.2 j-x.2 j)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      linarith [hcoord y hy i, hcoord y hy j, hdiam i j]
    exact hpair.trans (by nlinarith [mul_le_mul_of_nonneg_left hdist hC.le])
  have hηc' : η≤c/(4*(3*(3*C))^2) := by convert hηc using 1; ring
  have hj := sourceResidual_joint_jets_of_original_data hN x (3*C) H d c η
    (by positivity) hH hd hc hdH hη hη1 hηc' hUa hVa hTa
    (fun y hy i => (hVJa y hy i).trans (by linarith))
    (fun y hy i => (hT y.1 (y.2 i) (htime y hy) (hmem y hy i)).trans (by linarith))
    (fun i j => (hD0 i j).trans (by nlinarith [show 0≤C*H*d by positivity]))
    (fun i j => (hE0 i j).trans (by nlinarith [show 0≤C*d by positivity])) hR0 m
  convert hj using 1; ring

end
end IsingBulk.HT22

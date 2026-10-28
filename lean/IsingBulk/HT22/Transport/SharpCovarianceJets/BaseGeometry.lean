import IsingBulk.HT22.Transport.SharpCovarianceJets.PairBall
import IsingBulk.HT22.Transport.FieldNeighborhood.SmallDividedDifference

namespace IsingBulk.HT22.SharpCovarianceJets
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem sharp_jets_of_base_inverse_geometry {N : ℕ} (hN : 0<N)
    (x : SourcePoint N) (D : Set ℂ) (C H d c η : ℝ)
    (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c) (hdH : d≤H)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*(18*C)^2))
    (hD : Convex ℝ D)
    (hinside : ∀ i, closedBall (x.2 i) (η*d/(N:ℝ)^2) ⊆ D)
    (hU : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hVjet : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,q)‖≤C)
    (hTjet : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2) (t,q)‖≤C)
    (_hT : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D → ‖sourceInverseT t q‖≤C)
    (hV0 : ∀ i, ‖sourceInverseV x.1 (x.2 i)‖≤C*H)
    (hdiam : ∀ i j, ‖x.2 i-x.2 j‖≤d)
    (hR0 : c*H*d^2≤‖sourceCovariance x.1 x.2‖) (m : ℕ) :
    SharpBounds x C H d c η m := by
  let ρ := η*d/(N:ℝ)^2
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρd : ρ≤d := (div_le_self (by positivity) (one_le_pow₀ hn1)).trans
    (mul_le_of_le_one_left hd.le hη1)
  have htime (y : SourcePoint N) (hy : y∈closedBall x ρ) : ‖y.1-x.1‖≤ρ :=
    (norm_fst_le (y-x)).trans (by simpa only [mem_closedBall,dist_eq_norm] using hy)
  have hcoord (y : SourcePoint N) (hy : y∈closedBall x ρ) (a : Fin N) : ‖y.2 a-x.2 a‖≤ρ :=
    ((norm_le_pi_norm (y.2-x.2) a).trans (norm_snd_le (y-x))).trans
      (by simpa only [mem_closedBall,dist_eq_norm] using hy)
  have hmem (y : SourcePoint N) (hy : y∈closedBall x ρ) (a : Fin N) : y.2 a∈D :=
    hinside a (by simpa only [mem_closedBall,dist_eq_norm] using hcoord y hy a)
  have hUa (y : SourcePoint N) (hy : y∈closedBall x ρ) (a : Fin N) :=
    hU y.1 (y.2 a) (htime y hy) (hmem y hy a)
  have hVJa (y : SourcePoint N) (hy : y∈closedBall x ρ) (a : Fin N) :=
    hVjet y.1 (y.2 a) (htime y hy) (hmem y hy a)
  have hVa (y : SourcePoint N) (hy : y∈closedBall x ρ) (a : Fin N) :
      ‖sourceInverseV y.1 (y.2 a)‖≤2*C*H :=
    sourceInverseV_small_on_ball x y a ρ C H hρ.le (hρd.trans hdH) hC.le hy
      (fun z hz => hUa z hz a) (fun z hz => hVJa z hz a) (hV0 a)
  have hdiamY (y : SourcePoint N) (hy : y∈closedBall x ρ) (a b : Fin N) :
      ‖y.2 a-y.2 b‖≤3*d := by
    have he : y.2 a-y.2 b=(y.2 a-x.2 a)+(x.2 a-x.2 b)-(y.2 b-x.2 b) := by ring
    rw [he]
    have hh := (norm_sub_le ((y.2 a-x.2 a)+(x.2 a-x.2 b)) (y.2 b-x.2 b)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    linarith [hcoord y hy a,hcoord y hy b,hdiam a b]
  have hTa (y : SourcePoint N) (hy : y∈closedBall x ρ) (a b : Fin N) :
      ‖sourceInverseT y.1 (y.2 a)-sourceInverseT y.1 (y.2 b)‖≤3*C*d := by
    have hh := inverseT_pair_lipschitz y.1 (y.2 b) (y.2 a) D C hD (hmem y hy b) (hmem y hy a)
      (fun q hq => hU y.1 q (htime y hy) hq) (fun q hq => hTjet y.1 q (htime y hy) hq)
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (hdiamY y hy a b) hC.le])
  have hD1 (y : SourcePoint N) (hy : y∈closedBall x ρ) (a b : Fin N) :
      ‖fderiv ℂ (fun z => sourceInverseCoordinate a z-sourceInverseCoordinate b z) y‖≤(18*C)*H := by
    have hh := sourceInversePair_fderiv_bound y a b (3*C) H d (by positivity) hH.le hdH
      (hUa y hy) (fun a => (hVa y hy a).trans (by nlinarith [mul_nonneg hC.le hH.le]))
      (by simpa only [mul_assoc] using hTa y hy a b)
    exact hh.trans (by nlinarith [mul_nonneg hC.le hH.le])
  have hE1 (y : SourcePoint N) (hy : y∈closedBall x ρ) (a b : Fin N) :
      ‖fderiv ℂ (fun z => sourceInverseVCoordinate a z-sourceInverseVCoordinate b z) y‖≤18*C :=
    (sourceInverseVPair_fderiv_bound y a b C hC.le (hUa y hy) (hVJa y hy)).trans (by linarith)
  have hx : x∈closedBall x ρ := mem_closedBall_self hρ.le
  have htx : ‖x.1-x.1‖≤ρ := by simpa using hρ.le
  have hD0 (a b : Fin N) : ‖sourceInverseCoordinate a x-sourceInverseCoordinate b x‖≤(18*C)*H*d :=
    (regularInverse_pair_small x.1 (x.2 b) (x.2 a) D C H d hC.le hH.le hd.le hdH hD
      (hmem x hx b) (hmem x hx a) (hdiam a b) (fun q hq => hU x.1 q htx hq)
      (fun q hq => hVjet x.1 q htx hq) (hV0 b)).trans (by nlinarith [show 0≤C*H*d by positivity])
  have hE0 (a b : Fin N) : ‖sourceInverseVCoordinate a x-sourceInverseVCoordinate b x‖≤(18*C)*d := by
    have hh := inverseV_pair_lipschitz x.1 (x.2 b) (x.2 a) D C hD (hmem x hx b) (hmem x hx a)
      (fun q hq => hU x.1 q htx hq) (fun q hq => hVjet x.1 q htx hq)
    exact hh.trans ((mul_le_mul_of_nonneg_left (hdiam a b) hC.le).trans (by nlinarith [mul_nonneg hC.le hd.le]))
  have hmargin := sourceCovariance_margin_on_ball hN x (18*C) H d c η
    (by positivity) hH hd hc hη hη1 hηc hUa hD1 hE1 hD0 hE0 hR0
  have hRG :
      ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCovariance z.1 z.2) x‖≤
        (cauchyJetConstant m*(36*C)^2/η^m)*(N:ℝ)^(2*m+2)*H*d^2/d^m ∧
      ∀i, ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCentered z.1 z.2 i) x‖≤
        (cauchyJetConstant m*(36*C)/η^m)*(N:ℝ)^(2*m+1)*H*d/d^m := by
    apply pair_ball_jets hN x (36*C) H d η (by positivity) hH hd hη
      (fun y hy => hUa y (ball_subset_closedBall hy))
    · intro y hy a b
      have hyc := ball_subset_closedBall hy
      have hh := (convex_closedBall x ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((sourceInverseCoordinate_analyticAt z a (hUa z hz a)).sub
          (sourceInverseCoordinate_analyticAt z b (hUa z hz b))).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (fun z hz => hD1 z hz a b) hx hyc
      have hdist : ‖y-x‖≤d := (show ‖y-x‖≤ρ by simpa only [mem_closedBall,dist_eq_norm] using hyc).trans hρd
      have hb := hh.trans (mul_le_mul_of_nonneg_left hdist (by positivity : 0≤(18*C)*H))
      have ht := norm_sub_le (sourceInverseCoordinate a y-sourceInverseCoordinate b y-
        (sourceInverseCoordinate a x-sourceInverseCoordinate b x))
        (-(sourceInverseCoordinate a x-sourceInverseCoordinate b x))
      simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at ht
      change ‖sourceInverseCoordinate a y-sourceInverseCoordinate b y‖≤_
      simp only [Pi.sub_apply] at hb
      nlinarith [hD0 a b]
    · intro y hy a b
      have hyc := ball_subset_closedBall hy
      have hh := (convex_closedBall x ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((sourceInverseVCoordinate_analyticAt z a (hUa z hz a)).sub
          (sourceInverseVCoordinate_analyticAt z b (hUa z hz b))).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (fun z hz => hE1 z hz a b) hx hyc
      have hdist : ‖y-x‖≤d := (show ‖y-x‖≤ρ by simpa only [mem_closedBall,dist_eq_norm] using hyc).trans hρd
      have hb := hh.trans (mul_le_mul_of_nonneg_left hdist (by positivity : 0≤18*C))
      have ht := norm_sub_le (sourceInverseVCoordinate a y-sourceInverseVCoordinate b y-
        (sourceInverseVCoordinate a x-sourceInverseVCoordinate b x))
        (-(sourceInverseVCoordinate a x-sourceInverseVCoordinate b x))
      simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at ht
      change ‖sourceInverseVCoordinate a y-sourceInverseVCoordinate b y‖≤_
      simp only [Pi.sub_apply] at hb
      nlinarith [hE0 a b]
  exact ⟨hmargin,hRG.1,hRG.2,inverse_jets_of_margin hN x H d c η hH hd hc hη
    (fun y hy => hUa y (ball_subset_closedBall hy)) hmargin m⟩

end
end IsingBulk.HT22.SharpCovarianceJets

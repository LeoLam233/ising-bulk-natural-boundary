import IsingBulk.HT.Tail.NegativeCommonAllSectorParameters
import IsingBulk.HT.Tail.NegativeGeneralAllBranchWindow
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour
open Filter Asymptotics MeasureTheory
open scoped Topology

/-- Change only deformation parameters; the actual geometry is retained. -/
def withDeformation (seed : LocalBranchData) (tau alpha : ℝ)
    (htau : 0 < tau) (halpha : 0 < alpha) : LocalBranchData :=
  {seed with tau := tau,alpha := alpha,tau_pos := htau,alpha_pos := halpha}

theorem negative_ht_general_common_all_sector_parameters (seed : LocalBranchData)
    (hcseed : seed.c₀ < Real.sin seed.theta/2)
    (halg : IsAlgebraic ℚ (Complex.exp (-(seed.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ,1 ≤ N → Complex.exp (-(seed.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (p : ℕ) (hp : 1 ≤ p) (order : ℕ)
    (horder : order ≤ (p^2-1)/2) :
    ∃ (tau alpha : ℝ) (htau : 0 < tau) (halpha : 0 < alpha),
      Nonempty (NegativeHTCommonAllSectorParameters p
        (withDeformation seed tau alpha htau halpha) order) := by
  -- Only the geometry fields of this temporary data enter the four endpoints.
  let d₀ := seed
  have hc₀ : d₀.c₀ < Real.sin d₀.theta/2 :=
    hcseed
  obtain ⟨etaC, heC, hC⟩ := signed_ht_common_completed_sector_parameters (-1) (by norm_num) d₀ hc₀
  obtain ⟨etaS, heS, hS⟩ := signed_ht_common_source_summability (-1) (by norm_num) d₀ hc₀
  obtain ⟨etaM, heM, hM⟩ := signed_mixed_left_sector_sum_littleO Real.pi d₀ hc₀
  obtain ⟨etaR, heR, hR⟩ := signed_ht_compact_right_sector_sum_littleO Real.pi d₀ hc₀
  rw [negative_phase] at hM hR
  have hsin : 0 < Real.sin d₀.thetaB := d₀.a_pos
  let etaCap := min etaC (min etaS (min etaM (min etaR (Real.sin d₀.thetaB/4))))
  have heCap : 0 < etaCap :=
    lt_min heC (lt_min heS (lt_min heM (lt_min heR (by positivity))))
  let eta := etaCap/2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have het : eta < etaCap := by dsimp [eta]; linarith
  have heC' : eta < etaC := het.trans_le (min_le_left _ _)
  have heS' : eta < etaS := het.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heM' : eta < etaM := het.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heR' : eta < etaR := het.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hesmall : eta ≤ Real.sin d₀.thetaB/4 := het.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨alphaC, tauC, haC, htC, hC⟩ := hC eta heta heC'
  obtain ⟨alphaS, tauS, haS, htS, hS⟩ := hS eta heta heS'
  obtain ⟨alphaM, haM, hM⟩ := hM eta heta heM'
  obtain ⟨alphaR, tauR, haR, htR, hR⟩ := hR eta heta heR'
  let alphaCap := min alphaC (min alphaS (min alphaM (min alphaR (Real.sin d₀.thetaB/4))))
  have haCap : 0 < alphaCap :=
    lt_min haC (lt_min haS (lt_min haM (lt_min haR (by positivity))))
  let alpha := alphaCap/2
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have halt : alpha < alphaCap := by dsimp [alpha]; linarith
  have haC' : alpha < alphaC := halt.trans_le (min_le_left _ _)
  have haS' : alpha < alphaS := halt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haM' : alpha < alphaM := halt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haR' : alpha < alphaR := halt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hasmall : alpha < Real.sin d₀.thetaB/4 := halt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  -- The mixed threshold is chosen after alpha, as its source requires.
  obtain ⟨tauM, htM, hM⟩ := hM alpha halpha haM'
  let tauCap := min tauC (min tauS (min tauM tauR))
  have htCap : 0 < tauCap := lt_min htC (lt_min htS (lt_min htM htR))
  let tau := tauCap/2
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htlt : tau < tauCap := by dsimp [tau]; linarith
  have htC' : tau < tauC := htlt.trans_le (min_le_left _ _)
  have htS' : tau < tauS := htlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htM' : tau < tauM := htlt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htR' : tau < tauR := htlt.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let d := withDeformation seed tau alpha htau halpha
  obtain ⟨hregular, hF, hL, hK⟩ := hC alpha tau halpha haC' htau htC'
  have hsource := hS alpha tau halpha haS' htau htS'
  obtain ⟨outerB, hoB, hB⟩ := negative_ht_nonresonant_allBranch_window_littleO
    d halg hnot hcseed hasmall p hp
  obtain ⟨outerC, hoC, hzero⟩ := signed_constructed_current_all_branch_derivatives_zero (-1)
    d₀.thetaB_pos d₀.thetaB_lt heta hesmall
  let outer := min outerB outerC/2
  have houter : 0 < outer := by dsimp [outer]; positivity
  have hoB' : outer ≤ outerB := by
    have hh : 0 < min outerB outerC := lt_min hoB hoC
    have hhalf : min outerB outerC/2 ≤ min outerB outerC := by linarith
    exact hhalf.trans (min_le_left _ _)
  have hoC' : outer ≤ outerC := by
    have hh : 0 < min outerB outerC := lt_min hoB hoC
    have hhalf : min outerB outerC/2 ≤ min outerB outerC := by linarith
    exact hhalf.trans (min_le_right _ _)
  have hcos : Real.cos d₀.thetaB < 1 := by
    have hh := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨d₀.thetaB_pos.le, d₀.thetaB_lt.le⟩ d₀.thetaB_pos
    simpa only [Real.cos_zero] using hh
  let innerCap := 1-Real.cos d₀.thetaB
  have hiCap : 0 < innerCap := sub_pos.mpr hcos
  obtain ⟨inner₀, hi₀, hiCap', hM⟩ := hM tau htau htM' order outer innerCap houter hiCap
  let inner := inner₀/2
  have hinner : 0 < inner := by dsimp [inner]; positivity
  have hile : inner ≤ inner₀ := by dsimp [inner]; linarith
  have hismall : inner < 2*(1-Real.cos d₀.thetaB) := by
    have hh := hile.trans hiCap'
    change inner ≤ 1-Real.cos d₀.thetaB at hh
    change 0 < 1-Real.cos d₀.thetaB at hiCap
    linarith
  let beta := (1/4:ℝ)/((order:ℝ)+1)
  have hoReal : 0 < (order:ℝ)+1 := by positivity
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hbsmall : beta*((order:ℝ)+1) < 1/2 := by
    dsimp only [beta]
    rw [div_mul_cancel₀ _ (ne_of_gt hoReal)]
    norm_num
  have hbj (j : ℕ) (hj : j ≤ order) : beta*((j:ℝ)+1) < 1/2 := by
    have hjReal : (j:ℝ) ≤ (order:ℝ) := by exact_mod_cast hj
    exact (mul_le_mul_of_nonneg_left (by linarith : (j:ℝ)+1 ≤ (order:ℝ)+1) hbeta.le).trans_lt hbsmall
  obtain ⟨D, hD, hK⟩ := hK order 0 le_rfl
  have hsourceAll := finite_order_common_radius _ hsource order
  refine ⟨tau, alpha, htau, halpha, ⟨{
    eta := eta
    outer := outer
    inner := inner
    beta := beta
    D := D
    eta_pos := heta
    eta_small := hesmall
    alpha_small := hasmall
    outer_pos := houter
    inner_pos := hinner
    inner_small := hismall
    beta_pos := hbeta
    beta_small := hbsmall
    D_pos := hD
    c0_small := hcseed
    selector_regular := hregular
    current_allBranch_zero := ?_
    f_small := ?_
    large_small := ?_
    high_tendsto := ?_
    source_summability := hsourceAll
    allBranch_small := ?_
    mixedLeft_small := ?_
    rightCompact_small := ?_ }⟩⟩
  · intro N q r lam j s
    exact hzero outer houter hoC' alpha halpha hasmall N q r tau lam inner hinner j s
  · intro j _
    exact hF j
  · intro j hj
    exact hL j beta hbeta (hbj j hj)
  · intro j hj
    simpa only [Real.rpow_zero, div_one, signedHighKSNormTail, withDeformation, d₀] using
      hK j hj beta hbeta.le
  · intro j hj
    exact hB eta heta hesmall outer inner houter hinner hoB' D hD.le j (hj.trans horder)
  · intro j hj
    exact hM inner hinner hile j beta hj hbeta
  · intro j hj
    exact hR alpha tau halpha haR' htau htR' outer inner houter hinner hismall
      p j D beta hp (hj.trans horder) hD.le hbeta

end
end IsingBulk.HT.Tail

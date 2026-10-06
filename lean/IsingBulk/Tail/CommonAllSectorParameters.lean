import IsingBulk.Tail.CommonCompletedSectorParameters
import IsingBulk.Tail.CommonSourceSummability
import IsingBulk.Tail.AllBranchSectorAsymptotic
import IsingBulk.Tail.MixedLeftAsymptotic
import IsingBulk.Tail.CompactRightClosure
import IsingBulk.Tail.SectorCurrentExclusion

/-! One actual selected geometry and one selector for every sector in the
absolute-tail comparison. The estimates below are conclusions of the source
endpoints, not extra assumptions about a missing intermediate window. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.PrimeFamily
open Filter Asymptotics MeasureTheory
open scoped Topology

/-- A common, finite-order choice. `d` contains the actual chosen deformation
parameters; no equality between branch data with different parameters is used. -/
structure CommonAllSectorParameters (p : ℕ) (d : LocalBranchData) (order : ℕ) where
  eta : ℝ
  outer : ℝ
  inner : ℝ
  beta : ℝ
  D : ℝ
  eta_pos : 0 < eta
  eta_small : eta ≤ Real.sin d.thetaB/4
  alpha_small : d.alpha < Real.sin d.thetaB/4
  outer_pos : 0 < outer
  inner_pos : 0 < inner
  inner_small : inner < 2*(1-Real.cos d.thetaB)
  beta_pos : 0 < beta
  beta_small : beta*((order:ℝ)+1) < 1/2
  D_pos : 0 < D
  c0_small : d.c₀ < Real.sin d.theta/2
  selector_regular : RegularSelector (constructedSelector d.thetaB eta d.alpha)
  current_allBranch_zero : ∀ (N : ℕ) (q : Fin N) (r lam : ℝ) (j : ℕ) (s : ℂ),
    iteratedDeriv j (currentSectorIntegral N (constructedSelector d.thetaB eta d.alpha)
      r d.tau lam q d.thetaB outer inner outer_pos inner_pos none) s = 0
  f_small : ∀ j : ℕ, j ≤ order →
    (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j
      (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta d.alpha)
        (Real.exp (-d.c₀*eps)) d.tau) (radialParameter d.theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)
  large_small : ∀ j : ℕ, j ≤ order →
    (fun eps : ℝ => ∑' n : ℕ, ‖∫ lam in (eps^beta)..1,
      differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB eta d.alpha)
        (Real.exp (-d.c₀*eps)) d.tau lam j (radialParameter d.theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)
  high_tendsto : ∀ j : ℕ, j ≤ order →
    Tendsto (fun eps : ℝ => highKSNormTail d eta d.alpha d.tau j D eps (eps^beta))
      (𝓝[>] 0) (𝓝 0)
  source_summability : ∃ e : ℝ, 0 < e ∧ ∀ (j : ℕ), j ≤ order →
    ∀ eps cut : ℝ, 0 < eps → eps < e → 0 < cut → cut ≤ 1 →
      Summable (fun n : ℕ => ‖iteratedDeriv j
        (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta d.alpha)
          (Real.exp (-d.c₀*eps)) d.tau) (radialParameter d.theta eps)‖) ∧
      Summable (fun n : ℕ => ‖∫ lam in cut..1,
        differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB eta d.alpha)
          (Real.exp (-d.c₀*eps)) d.tau lam j (radialParameter d.theta eps)‖) ∧
      Summable (fun N : ℕ => if 2 ≤ N then
        originalKSNorm N (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps))
          d.tau j (radialParameter d.theta eps) cut else 0)
  allBranch_small : ∀ j : ℕ, j ≤ order →
    radialSeriesSmall (originalAllBranchWindowTerm p d eta outer inner outer_pos inner_pos D j)
  mixedLeft_small : ∀ j : ℕ, j ≤ order →
    radialSeriesSmall (fun eps N => mixedLeftSectorNorm N (constructedSelector d.thetaB eta d.alpha)
      (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner outer_pos inner_pos j
        (radialParameter d.theta eps) (eps^beta))
  rightCompact_small : ∀ j : ℕ, j ≤ order →
    radialSeriesSmall (fun eps N => compactRightWindow p D eps
      (fun N => rightCompactSectorNorm N (constructedSelector d.thetaB eta d.alpha)
        (Real.exp (-d.c₀*eps)) d.tau d.thetaB outer inner outer_pos inner_pos j
          (radialParameter d.theta eps) (eps^beta)) N)

/-- Shrinking positive radii makes finitely many eventual source estimates
simultaneous, with the radius chosen before `eps` and `cut`. -/
theorem finite_order_common_radius (P : ℕ → ℝ → ℝ → Prop)
    (hP : ∀ j : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ eps cut : ℝ,
      0 < eps → eps < e → 0 < cut → cut ≤ 1 → P j eps cut) (order : ℕ) :
    ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j ≤ order → ∀ eps cut : ℝ,
      0 < eps → eps < e → 0 < cut → cut ≤ 1 → P j eps cut := by
  induction order with
  | zero =>
      obtain ⟨e, he, hh⟩ := hP 0
      refine ⟨e, he, ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      exact hh
  | succ order ih =>
      obtain ⟨e, he, hh⟩ := ih
      obtain ⟨e', he', hh'⟩ := hP (order+1)
      refine ⟨min e e', lt_min he he', ?_⟩
      intro j hj eps cut heps helt hcut hcut1
      by_cases hjold : j ≤ order
      · exact hh j hjold eps cut heps (helt.trans_le (min_le_left _ _)) hcut hcut1
      · have hjeq : j = order+1 := by omega
        subst j
        exact hh' eps cut heps (helt.trans_le (min_le_right _ _)) hcut hcut1

/-- The source endpoints admit one acyclic common choice at every fixed
selected point and finite permitted derivative ceiling. -/
theorem common_all_sector_parameters {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (order : ℕ)
    (horder : order ≤ (2*p)^2/2-1) :
    ∃ (tau alpha : ℝ) (htau : 0 < tau) (halpha : 0 < alpha),
      Nonempty (CommonAllSectorParameters p
        (selectedLocalBranchData ha hb tau alpha htau halpha) order) := by
  -- Only the geometry fields of this temporary data enter the four endpoints.
  let d₀ := selectedLocalBranchData ha hb 1 1 zero_lt_one zero_lt_one
  have hc₀ : d₀.c₀ < Real.sin d₀.theta/2 :=
    selectedLocalBranchData_c0_small ha hb 1 1 zero_lt_one zero_lt_one
  obtain ⟨etaC, heC, hC⟩ := common_completed_sector_parameters d₀ hc₀
  obtain ⟨etaS, heS, hS⟩ := common_source_summability d₀ hc₀
  obtain ⟨etaM, heM, hM⟩ := mixed_left_sector_sum_littleO d₀ hc₀
  obtain ⟨etaR, heR, hR⟩ := compact_right_sector_sum_littleO d₀ hc₀
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
  let d := selectedLocalBranchData ha hb tau alpha htau halpha
  obtain ⟨hregular, hF, hL, hK⟩ := hC alpha tau halpha haC' htau htC'
  have hsource := hS alpha tau halpha haS' htau htS'
  obtain ⟨outerB, hoB, hB⟩ := selected_original_allBranch_window_littleO
    hp ha hb tau alpha htau halpha hasmall
  obtain ⟨outerC, hoC, hzero⟩ := constructed_current_all_branch_derivatives_zero
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
    c0_small := selectedLocalBranchData_c0_small ha hb tau alpha htau halpha
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
    simpa only [Real.rpow_zero, div_one, highKSNormTail, selectedLocalBranchData, d₀] using
      hK j hj beta hbeta.le
  · intro j hj
    exact hB eta heta hesmall outer inner houter hinner hoB' D hD.le j (hj.trans horder)
  · intro j hj
    exact hM inner hinner hile j beta hj hbeta
  · intro j hj
    exact hR alpha tau halpha haR' htau htR' outer inner houter hinner hismall
      p j D beta hp.one_lt.le (hj.trans horder) hD.le hbeta

end
end IsingBulk.Tail

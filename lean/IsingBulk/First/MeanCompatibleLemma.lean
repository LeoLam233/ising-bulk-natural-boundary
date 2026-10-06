import IsingBulk.First.MeanPhysicalLemma

/-! The physical mean endpoint accepts any prior positive mean-support
threshold, allowing independent localization and shape-integration domains to agree. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch Set
open scoped Topology

theorem actual_physical_mean_lemma_below (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) (L : ℝ) (hL : 0 < L) :
    ∃ delta R epsilon₀ : ℝ, 0 < delta ∧ delta ≤ L ∧ 0 < R ∧ 0 < epsilon₀ ∧
      ∀ eta : ℝ → ℂ, Continuous eta → (∀ x : ℝ, |x| ≤ delta → eta x=1) →
      (∀ (epsilon : ℝ) (t : Fin n → ℝ) (s : ℂ), 0 < epsilon → epsilon < epsilon₀ →
        (∀ j, |shapeExtend t j| < R/4) →
        ‖s-radialParameter a.theta epsilon‖ < (Real.sin a.theta/16)*epsilon →
        smoothMeanIntegral eta s (-(Real.sin a.theta/4)*epsilon) a.alpha delta t =
          postMeanDensity s a.alpha t +
            meanRegularError eta s (-(Real.sin a.theta/4)*epsilon) a.alpha delta t) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (epsilon : ℝ) (t : Fin n → ℝ) (s : ℂ),
        0 < epsilon → epsilon < epsilon₀ → (∀ i, |shapeExtend t i| < R/4) →
        ‖s-radialParameter a.theta epsilon‖ < (Real.sin a.theta/16)*epsilon →
        ‖(deriv^[j] (fun z => meanRegularError eta z (-(Real.sin a.theta/4)*epsilon)
          a.alpha delta t)) s‖ ≤ C) := by
  obtain ⟨Rg,hRg,_hRgpi,hRect⟩ := parameter_actual_mean_small_rectangle a n halpha
  obtain ⟨Rc,hRc,hReal⟩ := parameter_real_mean_continuous a n
  obtain ⟨D,hD,hError⟩ := actual_mean_regular_error_bounds a n halpha hbeta
  let delta := min L (min D (min Rg Rc/8))
  have hd : 0 < delta := lt_min hL (lt_min hD (div_pos (lt_min hRg hRc) (by norm_num)))
  have hdL : delta ≤ L := min_le_left _ _
  have hdD : delta ≤ D := (min_le_right _ _).trans (min_le_left _ _)
  have hdg : delta ≤ Rg/8 := ((min_le_right L (min D (min Rg Rc/8))).trans (min_le_right D (min Rg Rc/8))).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hdc : delta ≤ Rc/8 := ((min_le_right L (min D (min Rg Rc/8))).trans (min_le_right D (min Rg Rc/8))).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨rE,hrE,hErr⟩ := hError delta hd hdD
  let R := min Rg (min Rc rE)
  have hR : 0 < R := lt_min hRg (lt_min hRc hrE)
  have hRg' : R ≤ Rg := min_le_left _ _
  have hRc' : R ≤ Rc := (min_le_right _ _).trans (min_le_left _ _)
  have hRE : R ≤ rE := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨eM,heM,_,hM⟩ := radial_disk_source_trace_margin a.sin_theta_pos
  let c₀ := Real.sin a.theta/4
  let c₁ := Real.sin a.theta/16
  let K := c₀+c₁+1
  have hc₀ : 0 < c₀ := div_pos a.sin_theta_pos (by norm_num)
  have hc₁ : 0 < c₁ := div_pos a.sin_theta_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hNc : 0 < (n+1:ℝ)*c₀ := mul_pos (by positivity) hc₀
  let e₀ := min eM (min (R/K) (delta/((n+1:ℝ)*c₀)))
  have he₀ : 0 < e₀ := lt_min heM (lt_min (div_pos hR hK) (div_pos hd hNc))
  have hParams (epsilon : ℝ) (t : Fin n → ℝ) (s : ℂ) (he : 0 < epsilon)
      (her : epsilon < e₀) (ht : ∀ j, |shapeExtend t j| < R/4)
      (hs : ‖s-radialParameter a.theta epsilon‖ < c₁*epsilon) :
      ‖s-exp ((a.theta:ℂ)*I)‖ < R ∧ |(-c₀*epsilon)| < R ∧
      -c₀*epsilon < 0 ∧ -(n+1:ℝ)*(-c₀*epsilon) < delta ∧
      (Real.exp (-c₀*epsilon))⁻¹-Real.exp (-c₀*epsilon) < (sourceS s).im ∧
      ‖(-c₀*epsilon,t)‖ ≤ rE := by
    have heM' : epsilon < eM := her.trans_le (min_le_left _ _)
    have heK : epsilon < R/K := her.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have heN : epsilon < delta/((n+1:ℝ)*c₀) := her.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hKR : epsilon*K < R := (lt_div_iff₀ hK).mp heK
    have hscenter : ‖s-exp ((a.theta:ℂ)*I)‖ < R := by
      have htri := norm_sub_le_norm_sub_add_norm_sub s (radialParameter a.theta epsilon) (exp ((a.theta:ℂ)*I))
      rw [radialParameter_sub_center_norm,abs_of_pos he] at htri
      dsimp [K] at hKR
      nlinarith [mul_pos hc₀ he]
    have hrhoneg : -c₀*epsilon < 0 := by nlinarith [mul_pos hc₀ he]
    have hrho : |(-c₀*epsilon)| < R := by
      rw [abs_of_neg hrhoneg]
      dsimp [K] at hKR
      nlinarith [mul_pos hc₁ he]
    have hheight : -(n+1:ℝ)*(-c₀*epsilon) < delta := by
      have hm := (lt_div_iff₀ hNc).mp heN
      nlinarith
    have htn : ‖t‖ ≤ R/4 := shapeCoordinates_norm_le_of_extend_bound t (by positivity) (fun j => (ht j).le)
    have hpt : ‖(-c₀*epsilon,t)‖ ≤ rE := by
      rw [Prod.norm_def,Real.norm_eq_abs]
      exact max_le (hrho.le.trans hRE) (htn.trans (by linarith))
    exact ⟨hscenter,hrho,hrhoneg,hheight,(hM epsilon he heM' s hs).2,hpt⟩
  refine ⟨delta,R,e₀,hd,hdL,hR,he₀,?_⟩
  intro eta heta hinner
  obtain ⟨_haError,hbError⟩ := hErr eta heta
  constructor
  · intro epsilon t s he her ht hs
    obtain ⟨hsc,hrho,hrhoneg,hheight,hmargin,_htube⟩ := hParams epsilon t s he her ht hs
    have hres := hRect delta hd (by linarith) s (-c₀*epsilon) t
      (hsc.trans_le hRg') (hrho.trans_le hRg') hrhoneg hheight hmargin
      (fun j => (ht j).trans_le (by linarith))
    have hf := hReal s (-c₀*epsilon) t (hsc.trans_le hRc') (hrho.trans_le hRc')
      hrhoneg hmargin (fun j => (ht j).trans_le (by linarith))
    apply smoothMeanIntegral_eq_residue_add_error eta s (-c₀*epsilon) a.alpha delta t hd heta hinner ?_ hres
    exact hf.mono (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  · intro j
    obtain ⟨C,hC,hb⟩ := hbError j
    refine ⟨C,hC,?_⟩
    intro epsilon t s he her ht hs
    obtain ⟨hsc,_hrho,_hrhoneg,_hheight,_hmargin,htube⟩ := hParams epsilon t s he her ht hs
    exact hb (-c₀*epsilon) t htube s (hsc.trans_le hRE)

end
end IsingBulk.First

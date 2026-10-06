import IsingBulk.First.MeanCompatibleLemma
import IsingBulk.First.MeanFullIntegral
import IsingBulk.First.MeanShapeGap

/-! One source-facing physical mean endpoint, with common fixed support for
the genuine residue identity, every regular-error derivative, and nonlinear gap. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch
open scoped BigOperators Topology

/-- The manuscript physical mean conclusion for the actual source density.
The normalized y Jacobian is inside meanLocalDensity; N! and the fixed shape
cutoff remain outside this mean operation. -/
theorem physical_mean_residue (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) (L : ℝ) (hL : 0 < L) :
    ∃ delta h epsilon₀ c : ℝ, 0 < delta ∧ delta ≤ L ∧ 0 < h ∧ 0 < epsilon₀ ∧ 0 < c ∧
      ∀ eta : ℝ → ℂ, Continuous eta → (∀ x : ℝ, |x| ≤ delta → eta x=1) →
      (∀ x : ℝ, 2*delta < |x| → eta x=0) →
      (∀ (epsilon : ℝ) (t : Fin n → ℝ) (s : ℂ), 0 < epsilon → epsilon < epsilon₀ →
        (∑ i, (shapeExtend t i)^2) < h^2 →
        ‖s-radialParameter a.theta epsilon‖ < (Real.sin a.theta/16)*epsilon →
        (∫ v : ℝ, eta v * meanLocalDensity s (-(Real.sin a.theta/4)*epsilon) a.alpha t (v:ℂ)) =
          postMeanDensity s a.alpha t +
            meanRegularError eta s (-(Real.sin a.theta/4)*epsilon) a.alpha delta t) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (epsilon : ℝ) (t : Fin n → ℝ) (s : ℂ),
        0 < epsilon → epsilon < epsilon₀ → (∑ i, (shapeExtend t i)^2) < h^2 →
        ‖s-radialParameter a.theta epsilon‖ < (Real.sin a.theta/16)*epsilon →
        ‖(deriv^[j] (fun z => meanRegularError eta z (-(Real.sin a.theta/4)*epsilon)
          a.alpha delta t)) s‖ ≤ C) ∧
      (∀ (epsilon : ℝ) (t : Fin n → ℝ), 0 < epsilon → epsilon < epsilon₀ →
        (∑ i, (shapeExtend t i)^2) < h^2 →
        c*(epsilon+∑ i, (shapeExtend t i)^2) ≤
          ‖shapePoleDenominator (radialParameter a.theta epsilon) a.alpha t‖) := by
  obtain ⟨delta,R,eM,hd,hdL,hR,heM,hMean⟩ :=
    actual_physical_mean_lemma_below a n halpha hbeta L hL
  obtain ⟨c,rG,hc,hrG,hGap⟩ := actual_shape_denominator_lower_bound a n hbeta
  let h := min (R/4) rG
  have hh : 0 < h := lt_min (by positivity) hrG
  have hR' : h ≤ R/4 := min_le_left _ _
  have hG' : h ≤ rG := min_le_right _ _
  have hshape (t : Fin n → ℝ) (ht : (∑ i, (shapeExtend t i)^2) < h^2) (i : Fin (n+1)) :
      |shapeExtend t i| < h := by
    have hs : (shapeExtend t i)^2 ≤ ∑ j, (shapeExtend t j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [sq_abs (shapeExtend t i),abs_nonneg (shapeExtend t i)]
  refine ⟨delta,h,min eM rG,c,hd,hdL,hh,lt_min heM hrG,hc,?_⟩
  intro eta heta hinner hsupport
  obtain ⟨hId,hBound⟩ := hMean eta heta hinner
  refine ⟨?_,?_,?_⟩
  · intro epsilon t s he her ht hs
    rw [← smoothMeanIntegral_eq_full eta s (-(Real.sin a.theta/4)*epsilon) a.alpha delta t hd hsupport]
    exact hId epsilon t s he (her.trans_le (min_le_left _ _))
      (fun i => (hshape t ht i).trans_le hR') hs
  · intro j
    obtain ⟨C,hC,hb⟩ := hBound j
    exact ⟨C,hC,fun epsilon t s he her ht hs => hb epsilon t s he
      (her.trans_le (min_le_left _ _)) (fun i => (hshape t ht i).trans_le hR') hs⟩
  · intro epsilon t he her ht
    exact hGap epsilon t he (her.trans_le (min_le_right _ _))
      (fun i => (hshape t ht i).trans_le hG')

end
end IsingBulk.First

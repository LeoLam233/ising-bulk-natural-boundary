import IsingBulk.First.RegularDensityNeighborhood
import IsingBulk.First.ActualDensityExpansion

/-! Actual regular-chart density and pole jets, preserving every physical
source expression. Only required source-facing statements are generalized. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set Metric IsingBulk.Branch IsingBulk.First
open scoped Topology BigOperators

theorem actualLeadingAmplitude_eq (a : RegularChartData) (n k : ℕ)
    (s : ℂ) (t : Fin n → ℝ) :
    actualLeadingAmplitude a n k (s,t) = (actualSincFactor t:ℂ) *
      poleLeadingNumerator (fun z => actualRegularFactor z a.alpha t)
        (fun z => shapePoleDenominator z a.alpha t) k s / ((n+1).factorial:ℂ) := by rfl

theorem actualRemainderAmplitude_eq (a : RegularChartData) (n k : ℕ)
    (s : ℂ) (t : Fin n → ℝ) :
    actualRemainderAmplitude a n k (s,t) = (actualSincFactor t:ℂ) *
      poleRemainder (fun z => actualRegularFactor z a.alpha t)
        (fun z => shapePoleDenominator z a.alpha t) k s / ((n+1).factorial:ℂ) := by rfl

/-- Constants precede s and t. The only pointwise exception is the actual
pole D=0, where the totalized complex derivatives are not a physical boundary value. -/
theorem actual_postMean_derivative_expansion (a : RegularChartData) (n k : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (s : ℂ) (t : Fin n → ℝ),
      dist (s,t) (exp ((a.theta:ℂ)*I),0) < r → shapePoleDenominator s a.alpha t ≠ 0 →
      (deriv^[k] (fun z => postMeanDensity z a.alpha t/((n+1).factorial:ℂ))) s =
        2*(Real.pi:ℂ)*(firstVandermonde (shapeExtend t):ℂ)^2 *
          (actualLeadingAmplitude a n k (s,t)/(shapePoleDenominator s a.alpha t)^(k+1) +
            actualRemainderAmplitude a n k (s,t)/(shapePoleDenominator s a.alpha t)^k) := by
  obtain ⟨r,hr,hdom⟩ := actualDensityDomain_ball a n
  refine ⟨r,hr,?_⟩
  intro s t hp hne
  have hpoint := hdom (s,t) hp
  have hs : ∀ᶠ z : ℂ in 𝓝 s,
      dist (z,t) (exp ((a.theta:ℂ)*I),0) < r := by
    exact (continuous_id.prodMk continuous_const).continuousAt.eventually
      (isOpen_ball.mem_nhds hp)
  let c : ℂ := 2*(Real.pi:ℂ)*(firstVandermonde (shapeExtend t):ℂ)^2 *
    (actualSincFactor t:ℂ)/((n+1).factorial:ℂ)
  have heq : (fun z => postMeanDensity z a.alpha t/((n+1).factorial:ℂ)) =ᶠ[𝓝 s]
      (fun z => c*(actualRegularFactor z a.alpha t/shapePoleDenominator z a.alpha t)) := by
    filter_upwards [hs] with z hz
    have hh := hdom (z,t) hz
    rw [postMeanDensity_factorization z a.alpha t (fun i j _ => hh.2.2.1 i j)
      (fun i j _ => hh.2.2.2 i j)]
    dsimp [c]
    ring
  have hder := Filter.EventuallyEq.iteratedDeriv_eq k heq
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate] at hder
  rw [hder, iterate_deriv_const_mul]
  have hsplit := simplePole_expansion_analyticAt hpoint.1 hpoint.2.1 k hne
  simp only [hsplit, actualLeadingAmplitude_eq, actualRemainderAmplitude_eq]
  dsimp [c]
  ring

end
end IsingBulk.First.Regular

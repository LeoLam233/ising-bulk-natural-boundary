import IsingBulk.First.ActualDensityJets
import IsingBulk.First.ActualDensityNeighborhood
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The fixed-s derivative expansion is now instantiated on the literal
physical density on an actual common neighborhood, before shape rescaling. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Set Metric
open scoped Topology

theorem simplePole_expansion_analyticAt {B D : ℂ → ℂ} {s : ℂ}
    (hB : AnalyticAt ℂ B s) (hD : AnalyticAt ℂ D s) (k : ℕ) (hne : D s ≠ 0) :
    (deriv^[k] (fun z => B z/D z)) s =
      poleLeadingNumerator B D k s/(D s)^(k+1) + poleRemainder B D k s/(D s)^k := by
  obtain ⟨rB,hrB,hb⟩ := hB.exists_ball_analyticOnNhd
  obtain ⟨rD,hrD,hd⟩ := hD.exists_ball_analyticOnNhd
  exact iteratedDeriv_simplePole_expansion (isOpen_ball.inter isOpen_ball)
    (fun z hz => hb z hz.1) (fun z hz => hd z hz.2) k
    ⟨mem_ball_self hrB,mem_ball_self hrD⟩ hne

theorem actualLeadingAmplitude_eq (a : OrderedChartData) (n k : ℕ)
    (s : ℂ) (t : Fin n → ℝ) :
    actualLeadingAmplitude a n k (s,t) = (actualSincFactor t:ℂ) *
      poleLeadingNumerator (fun z => actualRegularFactor z a.alpha t)
        (fun z => shapePoleDenominator z a.alpha t) k s / ((n+1).factorial:ℂ) := by rfl

theorem actualRemainderAmplitude_eq (a : OrderedChartData) (n k : ℕ)
    (s : ℂ) (t : Fin n → ℝ) :
    actualRemainderAmplitude a n k (s,t) = (actualSincFactor t:ℂ) *
      poleRemainder (fun z => actualRegularFactor z a.alpha t)
        (fun z => shapePoleDenominator z a.alpha t) k s / ((n+1).factorial:ℂ) := by rfl

/-- Constants precede s and t. The only pointwise exception is the actual
pole D=0, where the totalized complex derivatives are not a physical boundary value. -/
theorem actual_postMean_derivative_expansion (a : OrderedChartData) (n k : ℕ) :
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
end IsingBulk.First

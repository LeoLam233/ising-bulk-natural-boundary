import IsingBulk.Preferred22.ActualWeightedVandermonde
import IsingBulk.Preferred22.WeightedPhysicalSource
import IsingBulk.Preferred22.PhysicalJacobianBound
import IsingBulk.Preferred22.VandermondeScale

/-! Actual fixed-order weighted right densities away from full equality.
The original smooth multiplier is differentiated by transport. Every scalar
factor is bounded from proved source jets, and the only remaining angular
majorant is the genuine occupancy-dependent Jacobian/resolvent. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem preferred_actual_weighted_away_density_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ ε₀ τ₀ δ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ →
      ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ n : ℕ,0<n → ∀ ψ : (Fin (2*n) → ℝ) → ℂ,ContDiff ℝ ∞ ψ →
      ∀ j : ℕ,∀ ρ : ℝ,0<ρ → ∃ C : ℝ,0<C ∧
      ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin (2*n) → ℝ,
      (∀ i,-δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      ρ≤preferredAngularDiameter θ →
      ‖preferredWeightedPhysicalDensity ψ τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
        C*preferredJacobianResolvent d B ε τ θ := by
  obtain ⟨capV,hcapV,hcapVa,hV⟩ := preferred_actual_weighted_vandermonde_bound d
  obtain ⟨capF,hcapF,_hcapFa,hF⟩ := preferred_actual_weighted_factorization d
  refine ⟨min capV capF,lt_min hcapV hcapF,(min_le_left _ _).trans_lt hcapVa,?_⟩
  intro B hBcap
  obtain ⟨εV,τV,δV,hεV,hτV,hδV,hδVB,hvb⟩ := hV B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δF,τF,εF,hδF,_hδFB,hτF,hεF,hfb⟩ := hF B (hBcap.trans_le (min_le_right _ _))
  obtain ⟨CJ,εJ,hCJ,hεJ,hjb⟩ := preferred_actual_JH_bound d B
  obtain ⟨CQ,hCQ,hqb⟩ := preferred_actual_coordinate_global_bound d B
  let ε₀ := min εV (min εF (min εJ 1))
  let τ₀ := min τV (min τF 1)
  let δ₀ := min δV δF
  have hε₀ : 0<ε₀ := lt_min hεV (lt_min hεF (lt_min hεJ zero_lt_one))
  have hτ₀ : 0<τ₀ := lt_min hτV (lt_min hτF zero_lt_one)
  have hδ₀ : 0<δ₀ := lt_min hδV hδF
  have hδ₀B : δ₀<B.delta := (min_le_left _ _).trans_lt hδVB
  refine ⟨ε₀,τ₀,δ₀,hε₀,hτ₀,hδ₀,hδ₀B,?_⟩
  intro δB hδB hδB₀ rcut hrcut hrcutp n hn ψ hψ j ρ hρ
  obtain ⟨CV,hCV,hvb'⟩ := hvb δB hδB (hδB₀.trans (min_le_left _ _))
    rcut hrcut hrcutp j n hn ψ hψ
  let N := 2*n
  have hN : 0<N := by dsimp only [N]; omega
  let A := CV/ρ^(2*j)*(2*CQ)^(N*(N-1))
  have hA : 0≤A := by dsimp only [A]; positivity
  refine ⟨2*CJ^N*A+1,by positivity,?_⟩
  intro ε τ hε hεr hτ hτr θ hθ hdiam
  have heV : ε<εV := hεr.trans_le (min_le_left _ _)
  have heF : ε<εF := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heJ : ε<εJ := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he1 : ε≤1 := (hεr.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))).le
  have htV : τ<τV := hτr.trans_le (min_le_left _ _)
  have htF : τ<τF := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht1 : τ≤1 := (hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hδBB : δB<B.delta := hδB₀.trans_lt hδ₀B
  have hθpi (i : Fin N) : θ i∈Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [(hθ i).1,(hθ i).2,B.branch_plateau,d.b_pos]
  have hθone (i : Fin N) : θ i∈Icc (-Real.pi-B.delta) B.delta :=
    ⟨by linarith [(hθpi i).1,B.delta_pos],by linarith [(hθ i).2]⟩
  have hθF : θ∈preferredRightAngularBox d B.delta δF N := by
    intro i
    have hdF : δB≤δF := hδB₀.trans (min_le_right _ _)
    exact ⟨by linarith [(hθ i).1],by linarith [(hθ i).2]⟩
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hq (i : Fin N) : ‖q i‖≤CQ := hqb N hN ε τ hε he1 hτ ht1 θ hθpi i
  have hΔ : ‖preferredSquaredVandermonde q‖≤(2*CQ)^(N*(N-1)) :=
    preferredSquaredVandermonde_norm_le q (fun i l =>
      (norm_sub_le _ _).trans (by linarith [hq i,hq l]))
  have hscalar : ‖preferredWeightedRegularScalar ψ τ preferredPopulationCutoff B.p B.m rcut j s θ‖≤A := by
    have hh := hvb' ε τ hε heV hτ htV θ hθ (hρ.trans_le hdiam)
    have hdiv : CV/preferredAngularDiameter θ^(2*j)≤CV/ρ^(2*j) :=
      div_le_div_of_nonneg_left hCV.le (pow_pos hρ _)
        (pow_le_pow_left₀ hρ.le hdiam _)
    exact hh.trans (mul_le_mul hdiv hΔ (norm_nonneg _) (by positivity))
  have hfactor := hfb N (by dsimp only [N]; omega) ε τ hε heF hτ htF θ hθF
    (hρ.trans_le hdiam) ψ hψ preferredPopulationCutoff rcut preferredPopulationCutoff_smooth hrcut j
  have hJ := hjb N hN ε τ hε heJ hτ ht1 θ hθone
  have hJR := preferredJacobianResolvent_nonneg d B ε τ θ
  rw [hfactor,norm_mul]
  calc
    _ ≤ (2*CJ^N*preferredJacobianResolvent d B ε τ θ)*A :=
      mul_le_mul hJ hscalar (norm_nonneg _) (by positivity)
    _ = (2*CJ^N*A)*preferredJacobianResolvent d B ε τ θ := by ring
    _ ≤ (2*CJ^N*A+1)*preferredJacobianResolvent d B ε τ θ :=
      mul_le_mul_of_nonneg_right (by linarith) hJR

end
end IsingBulk.Preferred22

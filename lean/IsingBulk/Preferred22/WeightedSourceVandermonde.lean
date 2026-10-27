import IsingBulk.Preferred22.WeightedTransportFactorization
import IsingBulk.Preferred22.SourceVandermonde

/-! Exact source Vandermonde factorization and finite-order quantitative
bounds for the actual weighted regular recurrence. Only derivatives of
the original smooth multiplier and source factors enter the estimates. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem preferred_weighted_source_full_vandermonde (n : ℕ)
    (ψ : (Fin (2*n) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (τ δ c : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin (2*n) → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hB : AnalyticAt ℂ (fun z : ℂ × (Fin (2*n) → ℂ) => preferredResidualCollective z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (hC : ∀ i j, AnalyticAt ℂ (fun z : ℂ × (Fin (2*n) → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j)
      (s,preferredSourceCoordinate τ p m s θ))
    (hgood : ∀ i j, PreferredRightRegularPoint c s
      (preferredSourceCoordinate τ p m s θ i) (preferredSourceCoordinate τ p m s θ j)) (j : ℕ) :
    preferredWeightedRegularScalar ψ τ η p m r j s θ=
      preferredVandermondeScalar τ p m (preferredSourceCollectiveDifference τ p m)
        (fun t x => ψ x*preferredVandermondeSeed τ η p m r t x) j s θ*
      preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  obtain ⟨Ω,hΩ,hz,hΩp,hΩB,hΩC,hΩg⟩ :=
    preferred_vandermonde_source_neighborhood τ δ c p m hp hm s θ hpoint hθ hB hC hgood
  have hbase := preferredMarkedBaseSmoothness_of_geometry τ δ η p m r hη hp hm hr Ω hΩ hΩp hΩB
  have hCm := preferredSourceCollectiveDifference_mixed τ δ p m hp hm Ω hΩp hΩC
  have hQm := preferredSourceKernelQuotient_mixed_of_good τ δ c p m hp hm Ω hΩp hΩg
  have hAm := hbase.2.2.2.mul (preferredVandermondeKernelAmplitude_source_mixed τ p m Ω hQm)
  have hψm : PreferredMixedSmoothOn (fun z : ℂ × (Fin (2*n) → ℝ) => ψ z.2) Ω := by
    intro z _
    refine ⟨(hψ.comp contDiff_snd).contDiffAt,?_⟩
    change DifferentiableAt ℂ (fun _ : ℂ => ψ z.2) z.1
    exact differentiableAt_const _
  exact preferredWeightedRegularScalar_vandermonde ψ τ δ η p m r hp hm _ _ Ω hΩ hΩp
    hbase.1 hbase.2.1 hCm (hψm.mul hAm)
    (fun z _ i j => preferredResidualCollective_difference_factor z.1 _ i j)
    (fun z hz => by
      rw [preferredRegularSeed_vandermonde n τ δ c η p m r z.1 z.2 (hΩp z hz) (hΩg z hz)]
      ring) j s θ hz


theorem preferred_weighted_source_vandermonde_bound (n : ℕ)
    (ψ : (Fin (2*n) → ℝ) → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (τ δ c : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin (2*n) → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hB : AnalyticAt ℂ (fun z : ℂ × (Fin (2*n) → ℂ) => preferredResidualCollective z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (hC : ∀ i j, AnalyticAt ℂ (fun z : ℂ × (Fin (2*n) → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j)
      (s,preferredSourceCoordinate τ p m s θ))
    (hgood : ∀ i j, PreferredRightRegularPoint c s
      (preferredSourceCoordinate τ p m s θ i) (preferredSourceCoordinate τ p m s θ j))
    (k : ℕ) (M A C B₀ C₀ D : ℝ) (hM : 0≤M) (hA : 0≤A) (hC1 : 1≤C) (hB₀ : 0≤B₀) (hC₀ : 0≤C₀)
    (hd : 0<preferredAngularDiameter θ) (hdD : preferredAngularDiameter θ≤D) (hD : 1≤D)
    (hψj : ∀ xs, xs.length≤k → ‖preferredFrameJet τ p m (fun _ x => ψ x) xs s θ‖≤M)
    (hAj : ∀ xs, xs.length≤k →
      ‖(((2*n).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n-1))*
        preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤A)
    (hQj : ∀ i j xs, xs.length≤k →
      ‖preferredFrameJet τ p m (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs))
    (hCj : ∀ i j xs, xs.length≤k →
      ‖preferredFrameJet τ p m (fun t x => preferredSourceCollectiveDifference τ p m t x i j) xs s θ‖≤
        C₀/preferredAngularDiameter θ^(2+preferredCoordinateJetOrder xs)) :
    ‖preferredWeightedRegularScalar ψ τ η p m r k s θ‖≤
      (((2^k*M)*(2^k*A*(2^k*((2^k*(2^k*C*C))^(2*n)))^(2*n))/
        ‖(((2*n).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n-1))‖)*D^k)*
      (D^2+2^k*(2*((2*n:ℕ):ℝ)*B₀+2*((2*n:ℕ):ℝ)^2*C₀))^k /
        preferredAngularDiameter θ^(2*k)*
      ‖preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ)‖ := by
  obtain ⟨Ω,hΩ,hz,hΩp,hΩB,hΩC,hΩg⟩ :=
    preferred_vandermonde_source_neighborhood τ δ c p m hp hm s θ hpoint hθ hB hC hgood
  have hbase := preferredMarkedBaseSmoothness_of_geometry τ δ η p m r hη hp hm hr Ω hΩ hΩp hΩB
  have hCm := preferredSourceCollectiveDifference_mixed τ δ p m hp hm Ω hΩp hΩC
  have hQm := preferredSourceKernelQuotient_mixed_of_good τ δ c p m hp hm Ω hΩp hΩg
  have hAm := hbase.2.2.2.mul (preferredVandermondeKernelAmplitude_source_mixed τ p m Ω hQm)
  have hBm (a : Fin (2*n)) : PreferredMixedSmoothOn
      (fun z => preferredResidualCollective z.1 (preferredSourceCoordinate τ p m z.1 z.2) a) Ω :=
    preferred_analytic_pullback_mixed τ δ p m hp hm Ω hΩp
      (fun z => preferredResidualCollective z.1 z.2 a) (fun z hz => analyticAt_pi_iff.mp (hΩB z hz) a)
  let Z : ℂ := ((2*n).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n-1)
  let A₀ := (2:ℝ)^k*A*(2^k*((2^k*(2^k*C*C))^(2*n)))^(2*n)/‖Z‖
  have hZ : 0<‖Z‖ := norm_pos_iff.mpr (preferred_seed_normalizer_ne_zero (2*n))
  have hA₀ : 0≤A₀ := by dsimp [A₀]; positivity
  have hAseed (xs : List (Option (Fin (2*n)))) (hxs : xs.length≤k) :
      ‖preferredFrameJet τ p m (preferredVandermondeSeed τ η p m r) xs s θ‖≤A₀ := by
    apply (le_div_iff₀ hZ).mpr
    have hh := preferredVandermondeSeed_frame_bound τ δ η p m r hη hp hm hr Ω hΩ hΩp hQm
      s θ hz k A C hA hC1 hAj hQj xs hxs
    rw [norm_mul] at hh
    simpa only [Z,mul_comm] using hh
  have hψm : PreferredMixedSmoothOn (fun z : ℂ × (Fin (2*n) → ℝ) => ψ z.2) Ω := by
    intro z _
    refine ⟨(hψ.comp contDiff_snd).contDiffAt,?_⟩
    change DifferentiableAt ℂ (fun _ : ℂ => ψ z.2) z.1
    exact differentiableAt_const _
  have hweighted (xs : List (Option (Fin (2*n)))) (hxs : xs.length≤k) :
      ‖preferredFrameJet τ p m (fun t x => ψ x*preferredVandermondeSeed τ η p m r t x) xs s θ‖≤
        2^k*M*A₀ :=
    preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hΩp (fun _ x => ψ x)
      (preferredVandermondeSeed τ η p m r) hψm hAm s θ hz k M A₀ hM hA₀ hψj hAseed xs hxs
  have hh := preferredVandermondeScalar_frame_bound τ δ p m hp hm _ _ Ω hΩ hΩp hBm hCm (hψm.mul hAm)
    s θ hz k (2^k*M*A₀) B₀ C₀ (preferredAngularDiameter θ) D (by positivity) hB₀ hC₀
    hd hdD hD hweighted hBj hCj k le_rfl [] (by simp)
  simp only [preferredFrameJet,preferredCoordinateJetOrder,List.countP_nil,add_zero] at hh
  rw [preferred_weighted_source_full_vandermonde n ψ hψ τ δ c η p m r hη hp hm hr s θ hpoint hθ hB hC hgood k,norm_mul]
  have hresult := mul_le_mul_of_nonneg_right hh
    (norm_nonneg (preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ)))
  convert hresult using 1
  dsimp only [A₀,Z]
  ring


end
end IsingBulk.Preferred22

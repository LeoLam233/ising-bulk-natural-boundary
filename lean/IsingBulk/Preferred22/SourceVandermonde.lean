import IsingBulk.Preferred22.VandermondeSeed
import IsingBulk.Preferred22.VandermondeNorm
import IsingBulk.Preferred22.CollectiveDifferenceJets

/-! Full squared-Vandermonde factorization and inverse-square scalar loss
at the genuine source. Local analytic data are checked for the original
collective and kernel factors, never assumed for generated descendants. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def preferredSourceCollectiveDifference {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N) : ℂ :=
  preferredCollectiveDifferenceFactor s (preferredSourceCoordinate τ p m s θ) i j

theorem preferred_vandermonde_source_neighborhood {N : ℕ}
    (τ δ c : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hB : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2)
      (s,preferredSourceCoordinate τ p m s θ))
    (hC : ∀ i j, AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j)
      (s,preferredSourceCoordinate τ p m s θ))
    (hgood : ∀ i j, PreferredRightRegularPoint c s
      (preferredSourceCoordinate τ p m s θ i) (preferredSourceCoordinate τ p m s θ j)) :
    ∃ Ω : Set (ℂ × (Fin N → ℝ)), IsOpen Ω ∧ (s,θ)∈Ω ∧
      (∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) ∧
      (∀ z∈Ω, AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2)) ∧
      (∀ z∈Ω, ∀ i j, AnalyticAt ℂ
        (fun x : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor x.1 x.2 i j)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2)) ∧
      (∀ z∈Ω, ∀ i j, PreferredRightRegularPoint c z.1
        (preferredSourceCoordinate τ p m z.1 z.2 i) (preferredSourceCoordinate τ p m z.1 z.2 j)) := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  have hχ := (preferredSourceCoordinate_contDiffAt τ p m hp hm s θ hpoint.trace_im hpoint.upper).continuousAt
  have hΨ : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) (s,θ) := continuousAt_fst.prodMk hχ
  have hBa := hΨ.tendsto.eventually hB.eventually_analyticAt
  have hCa : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), ∀ i j,
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor x.1 x.2 i j)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact hΨ.tendsto.eventually (hC i j).eventually_analyticAt
  have hGa : ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,θ), ∀ i j,
      PreferredRightRegularPoint c z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)
        (preferredSourceCoordinate τ p m z.1 z.2 j) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hmap : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
        (z.1,preferredSourceCoordinate τ p m z.1 z.2 i,
          preferredSourceCoordinate τ p m z.1 z.2 j)) (s,θ) :=
      continuousAt_fst.prodMk (((continuous_apply i).continuousAt.comp hχ).prodMk
        ((continuous_apply j).continuousAt.comp hχ))
    exact hmap.tendsto.eventually ((preferredRightRegularPoint_isOpen c).mem_nhds (hgood i j))
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp (hgeom.and (hBa.and (hCa.and hGa)))
  exact ⟨Ω,hΩ,hz,fun z hz => (hΩsub hz).1,fun z hz => (hΩsub hz).2.1,
    fun z hz => (hΩsub hz).2.2.1,fun z hz => (hΩsub hz).2.2.2⟩

theorem preferredSourceCollectiveDifference_mixed {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hC : ∀ z∈Ω, ∀ i j, AnalyticAt ℂ
      (fun x : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor x.1 x.2 i j)
      (z.1,preferredSourceCoordinate τ p m z.1 z.2)) :
    ∀ i j, PreferredMixedSmoothOn (fun z => preferredSourceCollectiveDifference τ p m z.1 z.2 i j) Ω := by
  intro i j
  exact preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint
    (fun z => preferredCollectiveDifferenceFactor z.1 z.2 i j) (fun z hz => hC z hz i j)

/-- Exact preservation of the full collision degree at every even order,
including all partial diagonals. -/
theorem preferred_source_full_vandermonde (n : ℕ)
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
    preferredRegularTransportedScalar τ η p m r j s θ=
      preferredVandermondeScalar τ p m (preferredSourceCollectiveDifference τ p m)
        (preferredVandermondeSeed τ η p m r) j s θ*
      preferredSquaredVandermonde (preferredSourceCoordinate τ p m s θ) := by
  obtain ⟨Ω,hΩ,hz,hΩp,hΩB,hΩC,hΩg⟩ :=
    preferred_vandermonde_source_neighborhood τ δ c p m hp hm s θ hpoint hθ hB hC hgood
  have hbase := preferredMarkedBaseSmoothness_of_geometry τ δ η p m r hη hp hm hr Ω hΩ hΩp hΩB
  have hCm := preferredSourceCollectiveDifference_mixed τ δ p m hp hm Ω hΩp hΩC
  have hQm := preferredSourceKernelQuotient_mixed_of_good τ δ c p m hp hm Ω hΩp hΩg
  have hAm := hbase.2.2.2.mul (preferredVandermondeKernelAmplitude_source_mixed τ p m Ω hQm)
  exact preferredRegularTransportedScalar_vandermonde τ δ η p m r hp hm _ _ Ω hΩ hΩp
    hbase.1 hbase.2.1 hCm hAm
    (fun z _ i j => preferredResidualCollective_difference_factor z.1 _ i j)
    (fun z hz => preferredRegularSeed_vandermonde n τ δ c η p m r z.1 z.2 (hΩp z hz) (hΩg z hz)) j s θ hz

/-- Quantitative complete-Vandermonde estimate from only the original
source seed, regular quotient, collective field and pair-factor jets. -/
theorem preferred_source_vandermonde_bound (n : ℕ)
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
    (k : ℕ) (A C B₀ C₀ D : ℝ) (hA : 0≤A) (hC1 : 1≤C) (hB₀ : 0≤B₀) (hC₀ : 0≤C₀)
    (hd : 0<preferredAngularDiameter θ) (hdD : preferredAngularDiameter θ≤D) (hD : 1≤D)
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
    ‖preferredRegularTransportedScalar τ η p m r k s θ‖≤
      (((2^k*A*(2^k*((2^k*(2^k*C*C))^(2*n)))^(2*n))/
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
  have hh := preferredVandermondeScalar_frame_bound τ δ p m hp hm _ _ Ω hΩ hΩp hBm hCm hAm
    s θ hz k A₀ B₀ C₀ (preferredAngularDiameter θ) D hA₀ hB₀ hC₀ hd hdD hD hAseed hBj hCj k le_rfl [] (by simp)
  simp only [preferredFrameJet,preferredCoordinateJetOrder,List.countP_nil,add_zero] at hh
  rw [preferred_source_full_vandermonde n τ δ c η p m r hη hp hm hr s θ hpoint hθ hB hC hgood k,norm_mul]
  exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)

end
end IsingBulk.Preferred22

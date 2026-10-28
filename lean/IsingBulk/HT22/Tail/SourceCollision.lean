import IsingBulk.HT22.Tail.CollisionBounds
import IsingBulk.HT22.Tail.PairSeedBounds

/-! Actual odd-border seed and collision recurrence at the physical source.
The shared scalar contains only the identical original seed and pair quotients;
its derivatives below always use the new fixed-v frame. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Set
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem sourcePairAmplitude_eq_shared {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    regularPairAmplitude s (sourceCoordinate τ p m s θ)=
      preferredVandermondeKernelAmplitude s (preferredSourceCoordinate τ p m s θ) := by
  simp only [regularPairAmplitude,regularPairQuotient,sourceCoordinate_moving_adapter,
    preferredVandermondeKernelAmplitude]

theorem sourcePairQuotient_eq_shared {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N) :
    regularPairQuotient s (sourceCoordinate τ p m s θ i) (sourceCoordinate τ p m s θ j)=
      preferredSourceKernelQuotient τ p m s θ i j := by
  simp only [regularPairQuotient,sourceCoordinate_moving_adapter,preferredSourceKernelQuotient]

theorem odd_regularSeed_vandermonde (n : ℕ) (τ δ c : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin (2*n+1) → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hgood : ∀ i j, PreferredRightRegularPoint c s
      (preferredSourceCoordinate τ p m s θ i) (preferredSourceCoordinate τ p m s θ j)) :
    regularSeed τ η p m r s θ=
      preferredVandermondeSeed τ η p m r s θ*
        preferredSquaredVandermonde (sourceCoordinate τ p m s θ) := by
  have hroot (i : Fin (2*n+1)) :
      ‖Complex.exp (-Complex.I*regularPhase s (sourceCoordinate τ p m s θ i))‖<1 := by
    rw [regularPhase_moving_adapter,sourceCoordinate_moving_adapter]
    exact hpoint.phase_inside i
  have hφ (i : Fin (2*n+1)) :
      (regularPhase s (sourceCoordinate τ p m s θ i)).im<0 := by
    rw [regularPhase_moving_adapter,sourceCoordinate_moving_adapter]
    exact hpoint.phase_im_neg i
  unfold regularSeed sourceBorderedKernel
  rw [odd_regularBorderedKernel_vandermonde n c s _
    (by simpa only [sourceCoordinate_moving_adapter] using hgood) hroot hφ,
    sourcePairAmplitude_eq_shared,regularSeedCoefficient_eq_shared]
  change _ = (_*_)*_
  change _* (preferredSquaredVandermonde _ * _)=_
  ring

def sourcePairSlope {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i j : Fin N) : ℂ :=
  residualPairSlope s (sourceCoordinate τ p m s θ) i j

/-- Actual odd scalar factorization on an open source chart, using only
original field regularity and original pair-domain geometry. -/
theorem odd_source_full_vandermonde (n : ℕ)
    (τ δ c : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin (2*n+1) → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hCm : ∀ i j, PreferredMixedSmoothOn (fun z => sourcePairSlope τ p m z.1 z.2 i j) Ω)
    (hgood : ∀ z∈Ω, ∀ i j, PreferredRightRegularPoint c z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i) (preferredSourceCoordinate τ p m z.1 z.2 j))
    (j : ℕ) (s : ℂ) (θ : Fin (2*n+1) → ℝ) (hz : (s,θ)∈Ω) :
    regularTransportedScalar τ η p m r j s θ=
      vandermondeScalar τ p m (sourcePairSlope τ p m)
        (preferredVandermondeSeed τ η p m r) j s θ*
        preferredSquaredVandermonde (sourceCoordinate τ p m s θ) := by
  obtain ⟨hV,hc⟩ := source_generator_mixed τ δ p m hp hm Ω hΩ hpoint hR
  have hQm := preferredSourceKernelQuotient_mixed_of_good τ δ c p m hp hm Ω hpoint hgood
  have hAm := (preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint).mul
    (preferredVandermondeKernelAmplitude_source_mixed τ p m Ω hQm)
  exact regularTransportedScalar_vandermonde τ δ η p m r hp hm _ _ Ω hΩ hpoint
    hV hc hCm hAm (fun z _ i j => residualField_difference z.1 _ i j)
    (fun z hz => odd_regularSeed_vandermonde n τ δ c η p m r z.1 z.2 (hpoint z hz) (hgood z hz))
    j s θ hz

/-- Near scalar estimate: all inputs are jets of the original seed,
removable pair quotient, new mixed field and its exact pair slope. -/
theorem odd_source_vandermonde_bound (n : ℕ)
    (τ δ c : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin (2*n+1) → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (hCm : ∀ i j, PreferredMixedSmoothOn (fun z => sourcePairSlope τ p m z.1 z.2 i j) Ω)
    (hgood : ∀ z∈Ω, ∀ i j, PreferredRightRegularPoint c z.1
      (preferredSourceCoordinate τ p m z.1 z.2 i) (preferredSourceCoordinate τ p m z.1 z.2 j))
    (s : ℂ) (θ : Fin (2*n+1) → ℝ) (hz : (s,θ)∈Ω)
    (k : ℕ) (A C B₀ C₀ Δ D : ℝ) (hA : 0≤A) (hC1 : 1≤C) (hB₀ : 0≤B₀) (hC₀ : 0≤C₀)
    (hd : 0<Δ) (hdD : Δ≤D) (hD : 1≤D)
    (hAj : ∀ xs, xs.length≤k →
      ‖(((2*n+1).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n))*
        frameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤A)
    (hQj : ∀ i j xs, xs.length≤k →
      ‖frameJet τ p m (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C)
    (hBj : ∀ a xs, xs.length≤k+1 →
      ‖frameJet τ p m (fun t x => residualField t (sourceCoordinate τ p m t x) a) xs s θ‖≤
        B₀/Δ^(1+xs.length))
    (hCj : ∀ i j xs, xs.length≤k →
      ‖frameJet τ p m (fun t x => sourcePairSlope τ p m t x i j) xs s θ‖≤
        C₀/Δ^(2+xs.length)) :
    ‖regularTransportedScalar τ η p m r k s θ‖≤
      (((2^k*A*(2^k*((2^k*(2^k*C*C))^(2*n+1)))^(2*n+1))/
        ‖(((2*n+1).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n))‖)*D^k)*
      (D^2+2^k*(2*((2*n+1:ℕ):ℝ)*B₀+2*((2*n+1:ℕ):ℝ)^2*C₀))^k / Δ^(2*k)*
      ‖preferredSquaredVandermonde (sourceCoordinate τ p m s θ)‖ := by
  have hQm := preferredSourceKernelQuotient_mixed_of_good τ δ c p m hp hm Ω hpoint hgood
  have hAm := (preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hpoint).mul
    (preferredVandermondeKernelAmplitude_source_mixed τ p m Ω hQm)
  have hBm := (source_generator_factors_mixed τ δ p m hp hm Ω hpoint hR).2.2.2
  let Z : ℂ := ((2*n+1).factorial:ℂ)*(2*Real.pi:ℂ)^(2*n)
  let A₀ := (2:ℝ)^k*A*(2^k*((2^k*(2^k*C*C))^(2*n+1)))^(2*n+1)/‖Z‖
  have hZ : 0<‖Z‖ := by
    exact norm_pos_iff.mpr (by simpa only [Nat.add_sub_cancel] using preferred_seed_normalizer_ne_zero (2*n+1))
  have hA₀ : 0≤A₀ := by dsimp [A₀]; positivity
  have hAseed (xs : List (Option (Fin (2*n+1)))) (hxs : xs.length≤k) :
      ‖frameJet τ p m (preferredVandermondeSeed τ η p m r) xs s θ‖≤A₀ := by
    apply (le_div_iff₀ hZ).mpr
    have hh := pairSeed_frame_bound τ δ η p m r hη hp hm hr Ω hΩ hpoint hR hQm
      s θ hz k A C hA hC1 (by simpa only [Nat.add_sub_cancel] using hAj) hQj xs hxs
    rw [norm_mul] at hh
    simpa only [Z,Nat.add_sub_cancel,mul_comm] using hh
  have hh := vandermondeScalar_frame_bound τ δ p m hp hm _ _ Ω hΩ hpoint hR hBm hCm hAm
    s θ hz k A₀ B₀ C₀ Δ D hA₀ hB₀ hC₀ hd hdD hD hAseed hBj hCj k le_rfl [] (by simp)
  simp only [frameJet,List.length_nil,add_zero] at hh
  rw [odd_source_full_vandermonde n τ δ c η p m r hη hp hm hr Ω hΩ hpoint hR hCm hgood k s θ hz,norm_mul]
  exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)

end
end IsingBulk.HT22.Tail

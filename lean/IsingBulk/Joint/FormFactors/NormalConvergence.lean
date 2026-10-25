import IsingBulk.Joint.FormFactors.NormalEnvelope
import IsingBulk.Joint.FormFactors.FiniteHolomorphy
import IsingBulk.Joint.FormFactors.NormalJets
import IsingBulk.Joint.FormFactors.Normalized
import IsingBulk.Joint.Geometry.SpectralComplement

/-! Actual all-particle JOINT normal convergence and holomorphy. Every
coefficient remains the literal full-site double contour, including the
origin; parity and normalization are exactly JOINT (3.10)--(3.11). -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter
open scoped Topology
open IsingBulk.Anisotropic.FormFactors (hadamardEnvelope hadamardEnvelope_odd_summable
  hadamardEnvelope_even_summable)

def particleTerm (N k : ℕ → ℕ) (n : ℕ) (K : Coupling) : ℂ :=
  p K^(k n)*unscaledFullCoefficient (N n) K

theorem particleTerm_contDiffAt (N k : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (i j : ℕ) {K : Coupling} (hK : K ∉ spectralSet) :
    ContDiffAt ℂ j (particleTerm N k i) K :=
  ((p_analyticAt K).contDiffAt.pow _).mul (unscaledFullCoefficient_contDiffAt j _ (hN i) hK)

theorem selected_particleSeries_contDiffAt (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    (j : ℕ) {K : Coupling} (hK : K ∉ spectralSet) :
    ContDiffAt ℂ j (fun L => ∑' n, particleTerm N k n L) K := by
  obtain ⟨U,hUK,hU,hUc,M,hM,hb⟩ := local_weighted_envelope N k hN hk hs hK
  exact normalSeries_contDiffAt j hU
    (fun i j L hL => particleTerm_contDiffAt N k hN i j (hUc hL))
    hM hb (mem_of_mem_nhds hUK)

theorem selected_particleSeries_all_mixed_derivatives (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    (j : ℕ) {K : Coupling} (hK : K ∉ spectralSet) :
    HasSum (fun n => iteratedFDeriv ℂ j (particleTerm N k n) K)
      (iteratedFDeriv ℂ j (fun L => ∑' n, particleTerm N k n L) K) := by
  obtain ⟨U,hUK,hU,hUc,M,hM,hb⟩ := local_weighted_envelope N k hN hk hs hK
  exact normalSeries_iteratedFDeriv_hasSum j hU
    (fun i j L hL => particleTerm_contDiffAt N k hN i j (hUc hL))
    hM hb (mem_of_mem_nhds hUK)

theorem selected_particleSeries_local_normal_jets (N k : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hk : ∀ n, k n ≤ N n)
    (hs : ∀ C : ℝ, 0 ≤ C → Summable (fun n => hadamardEnvelope C (N n)))
    (j : ℕ) {K : Coupling} (hK : K ∉ spectralSet) :
    ∃ V ∈ 𝓝 K, IsOpen V ∧ V ⊆ spectralSetᶜ ∧ ∃ M : ℕ → ℝ, Summable M ∧
      ∀ n L, L ∈ V → ‖iteratedFDeriv ℂ j (particleTerm N k n) L‖ ≤ M n := by
  obtain ⟨U,hUK,hU,hUc,M,hM,hb⟩ := local_weighted_envelope N k hN hk hs hK
  obtain ⟨V,hVK,hV,hVU,M',hM',hb'⟩ := normalSeries_local_jet_bound j hU
    (fun i j L hL => particleTerm_contDiffAt N k hN i j (hUc hL))
    hM hb (mem_of_mem_nhds hUK)
  exact ⟨V,hVK,hV,hVU.trans hUc,M',hM',hb'⟩

theorem even_positive_hadamard_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun n => hadamardEnvelope C (2*n+2)) := by
  have hh := (hadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective
  change Summable (fun n => hadamardEnvelope C (2*(n+1))) at hh
  simpa only [mul_add,mul_one] using hh

theorem high_particleSeries_contDiffAt (j : ℕ) {K : Coupling} (hK : K ∉ spectralSet) :
    ContDiffAt ℂ j (fun L => ∑' n : ℕ, p L^n*unscaledFullCoefficient (2*n+1) L) K :=
  selected_particleSeries_contDiffAt (fun n => 2*n+1) id
    (fun _ => by omega) (fun _ => by dsimp; omega)
    (fun _ hC => hadamardEnvelope_odd_summable hC) j hK

theorem low_particleSeries_contDiffAt (j : ℕ) {K : Coupling} (hK : K ∉ spectralSet) :
    ContDiffAt ℂ j (fun L => ∑' n : ℕ, p L^(n+1)*unscaledFullCoefficient (2*n+2) L) K :=
  selected_particleSeries_contDiffAt (fun n => 2*n+2) (fun n => n+1)
    (fun _ => by omega) (fun _ => by omega)
    (fun _ hC => even_positive_hadamard_summable hC) j hK

theorem highNormalizedBulk_contDiffAt (j : ℕ) {K : Coupling} (hK : K ∈ highDomain) :
    ContDiffAt ℂ j highNormalizedBulk K :=
  (highPrefactor_analyticOnNhd K hK).contDiffAt.mul
    (high_particleSeries_contDiffAt j (highDomain_subset_spectralComplement hK))

theorem lowNormalizedBulk_contDiffAt (j : ℕ) {K : Coupling} (hK : K ∈ lowDomain) :
    ContDiffAt ℂ j lowNormalizedBulk K :=
  (lowPrefactor_analyticOnNhd K hK).contDiffAt.mul
    (low_particleSeries_contDiffAt j (lowDomain_subset_spectralComplement hK))

theorem highNormalizedBulk_differentiableOn :
    DifferentiableOn ℂ highNormalizedBulk highDomain :=
  fun _ hK => (highNormalizedBulk_contDiffAt 1 hK).differentiableAt_one.differentiableWithinAt

theorem lowNormalizedBulk_differentiableOn :
    DifferentiableOn ℂ lowNormalizedBulk lowDomain :=
  fun _ hK => (lowNormalizedBulk_contDiffAt 1 hK).differentiableAt_one.differentiableWithinAt

end
end IsingBulk.Joint.FormFactors

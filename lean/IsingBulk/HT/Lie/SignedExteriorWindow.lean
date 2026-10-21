import IsingBulk.HT.Lie.SignedFiniteOrders
import IsingBulk.HT.Lie.ExteriorWindow

/-! The full signed allbranch exterior angular superseries, at the HT order
and odd-particle threshold. This theorem uses the actual signed physical
angular chart, not the unsigned LT source. Every lower analytic, cutoff,
coarea and spectator estimate has been attached before summing N. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Branch IsingBulk.Tail Filter Asymptotics
open scoped Topology

/-- Literal signed near/far angular sectors with the HT window threshold. -/
def htSignedExteriorWindowTerm (α : ℝ) (p : ℕ) (d : LocalBranchData) (η δ : ℝ)
    (hδ : 0 < δ) (A c β D : ℝ) (j : ℕ) (ε : ℝ) (N : ℕ) : ℝ :=
  if p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/ε)) then
    signedExteriorAngularNorm (Complex.exp (Complex.I*(α:ℂ))) N d η δ ε (allBranchMicroRadius A c N)
      (allBranchEqualityRadius β N) hδ j else 0

theorem htSignedExteriorWindowTerm_nonneg (α : ℝ) (p : ℕ) (d : LocalBranchData)
    (η δ : ℝ) (hδ : 0 < δ) (A c β D : ℝ) (j : ℕ) (ε : ℝ) (N : ℕ) :
    0 ≤ htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε N := by
  unfold htSignedExteriorWindowTerm
  split_ifs
  · exact signedExteriorAngularNorm_nonneg ..
  · exact le_rfl

/-- A single width and equality-scale threshold serve every HT derivative
order. The entire intermediate all-integer superseries is controlled, not
a fixed-N limit or a finite numerical jet. -/
theorem ht_signed_exterior_window_littleO (α : ℝ) {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2)
    (hα : d.alpha < Real.sin d.thetaB/4) (p : ℕ) (hp : 1 ≤ p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ A c : ℝ, 0 ≤ A → 0 < c → c ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      ∀ D : ℝ, 0 ≤ D → ∀ j : ℕ, j ≤ (p^2-1)/2 →
      (∀ᶠ ε : ℝ in 𝓝[>] 0,
        Summable (htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε)) ∧
      (fun ε : ℝ => ∑' N : ℕ,
        htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε N)
        =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
  obtain ⟨δ₀,hδ₀,hfinite⟩ :=
    signed_exterior_angular_window_finite α B hcsmall hα ((p^2-1)/2)
  refine ⟨δ₀,hδ₀,?_⟩
  intro η δ hδ hδsmall A c hA hc hc1
  obtain ⟨β₀,hβ₀,hβall⟩ := hfinite η δ hδ hδsmall A c hA hc hc1
  refine ⟨β₀,hβ₀,?_⟩
  intro β hβ D hD j hj
  obtain ⟨S,hS,hSn,hbound⟩ := hβall β hβ j hj
  have hmajor : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ N : ℕ,
      htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε N ≤
        S N*(Real.log (1/ε)+1)^2 := by
    filter_upwards [log_inverse_tendsto_atTop.eventually (hbound D hD),
      self_mem_nhdsWithin] with ε he hε
    intro N
    unfold htSignedExteriorWindowTerm
    split_ifs with hwindow
    · have hN : 1 ≤ N := by omega
      have hpred : N-1+1 = N := Nat.sub_add_cancel hN
      have hpreal : ((N-1:ℕ):ℝ)+1 = N := by exact_mod_cast hpred
      have horder := exterior_source_degree hp hwindow.1 hj
      have ho : 2*j+1 ≤ (N-1+1)*(N-1) := by rw [hpred]; exact horder
      have hh := he (N-1) (by rw [hpreal]; exact hwindow.2) ho
      have heq : Real.exp (-Real.log (1/ε)) = ε := by
        rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]
      simpa only [hpred,heq] using hh
    · exact mul_nonneg (hSn N) (sq_nonneg _)
  have hn := htSignedExteriorWindowTerm_nonneg α p d η δ hδ A c β D j
  have hsum : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Summable (htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε) := by
    filter_upwards [hmajor] with ε he
    exact Summable.of_nonneg_of_le (hn ε) he (hS.mul_right _)
  refine ⟨hsum,?_⟩
  have hO : (fun ε : ℝ => ∑' N : ℕ,
      htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε N)
      =O[𝓝[>] 0] (fun ε : ℝ => (Real.log (1/ε)+1)^2) := by
    apply IsBigO.of_bound (∑' N, S N)
    filter_upwards [hmajor,hsum] with ε he hsε
    have hh := Summable.tsum_le_tsum he hsε (hS.mul_right _)
    rw [tsum_mul_right] at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (hn ε)),
      abs_of_nonneg (sq_nonneg (Real.log (1/ε)+1))] using hh
  exact hO.trans_isLittleO radial_log_polynomial_littleO

/-- The branch-estimate bundle is constructed from the dispersion theorem,
not supplied as a new analytic interface by the HT caller. -/
theorem ht_signed_exterior_window_littleO_from_dispersion (α : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2)
    (hα : d.alpha < Real.sin d.thetaB/4) (p : ℕ) (hp : 1 ≤ p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ A c : ℝ, 0 ≤ A → 0 < c → c ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      ∀ D : ℝ, 0 ≤ D → ∀ j : ℕ, j ≤ (p^2-1)/2 →
      (∀ᶠ ε : ℝ in 𝓝[>] 0,
        Summable (htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε)) ∧
      (fun ε : ℝ => ∑' N : ℕ,
        htSignedExteriorWindowTerm α p d η δ hδ A c β D j ε N)
        =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
  obtain ⟨B⟩ := lemma_branch d
  exact ht_signed_exterior_window_littleO α B hcsmall hα p hp

end
end IsingBulk.HT.Lie

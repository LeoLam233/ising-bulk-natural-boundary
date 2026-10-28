import IsingBulk.HT22.Geometry.RegularFinitePartition
import IsingBulk.HT22.Geometry.BalancedEqualityCharts
import IsingBulk.HT22.Geometry.SignedEqualityArithmetic

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Metric IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic LocalLimit IsingBulk.Branch
open scoped BigOperators

/-- Actual lower-order signed local chart bounds, with both the regular
phase and the nonresonance gap proved from the selected source geometry. -/
theorem lower_regular_signed_local_bound {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a))
    (n : ℕ) (hodd : Odd (n+1)) (hnp : n+1<p) {g τ : ℝ} (hg : 0<g) (hτ : 0≤τ)
    (l : ℤ) (hl : l∈regularSignedMeanIndices d B negative (n+1) g) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,Continuous χ →
      (∀ u,χ u≠0 → ‖u‖<R) → ∀ j : ℕ,
      ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖(deriv^[j] (fun t => ∫ u,χ u*Physical.complexSignedDensity negative
        (t,balancedEqualityChart τ B.p B.m (signedEqualityMean negative (n+1) l) u)))
          (radialParameter d.alpha ε)‖≤C := by
  have hmean := (Finset.mem_filter.mp hl).2
  obtain ⟨β,hβ,hβπ,hrel⟩ := right_mean_regular_phase d (by positivity : 0<g/4)
    (by linarith [B.delta_b,d.b_pos] : B.delta<d.b) hmean
  have hlevel : Real.cos (signedEqualityMean negative (n+1) l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a) := by
    cases negative <;> simp only [Bool.false_eq_true,↓reduceIte] at hcos ⊢ <;> linarith
  have hgap := lower_signed_equality_product_gap hp hp5 ha (by omega : 0<n+1) hodd hnp negative l β hlevel
  exact balanced_signed_local_derivatives_bounded n negative d B hτ
    (signedEqualityMean negative (n+1) l) β hβ hβπ hrel hgap

/-- At first order every regular mean other than the unique lower
critical center has bounded actual contour derivatives of every order. -/
theorem first_other_regular_signed_local_bound {p n : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hn : n+1=p) {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a))
    {g τ : ℝ} (hg : 0<g) (hτ : 0≤τ) (l : ℤ)
    (hl : l∈regularSignedMeanIndices d B negative (n+1) g)
    (hother : signedEqualityMean negative (n+1) l≠ -d.alpha) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,Continuous χ →
      (∀ u,χ u≠0 → ‖u‖<R) → ∀ j : ℕ,
      ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖(deriv^[j] (fun t => ∫ u,χ u*Physical.complexSignedDensity negative
        (t,balancedEqualityChart τ B.p B.m (signedEqualityMean negative (n+1) l) u)))
          (radialParameter d.alpha ε)‖≤C := by
  have hmean := (Finset.mem_filter.mp hl).2
  obtain ⟨β,hβ,hβπ,hrel⟩ := right_mean_regular_phase d (by positivity : 0<g/4)
    (by linarith [B.delta_b,d.b_pos] : B.delta<d.b) hmean
  have hlevel : Real.cos (signedEqualityMean negative p l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a) := by
    rw [hn] at hrel
    cases negative <;> simp only [Bool.false_eq_true,↓reduceIte] at hcos ⊢ <;> linarith
  have hgap : 1-Physical.constraintSign negative*(Complex.exp (-(β:ℂ)*Complex.I))^(n+1)≠0 := by
    intro hz
    apply hother
    rw [hn] at hz ⊢
    apply first_signed_right_equality_unique hp hp5 ha negative l β d B hcos hlevel _ (sub_eq_zero.mp hz).symm
    rw [←hn]
    exact ⟨by linarith [hmean.1,d.b_lt,B.delta_pos],hmean.2⟩
  exact balanced_signed_local_derivatives_bounded n negative d B hτ
    (signedEqualityMean negative (n+1) l) β hβ hβπ hrel hgap

end
end IsingBulk.HT22.Geometry

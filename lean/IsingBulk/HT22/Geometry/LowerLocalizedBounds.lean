import IsingBulk.HT22.Geometry.LocalizedSignedBounds
import IsingBulk.HT22.Geometry.RegularSignedLocalBounds

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic LocalLimit IsingBulk.Branch
open scoped BigOperators

theorem positive_geometry_branch_identity (d : PreferredBranchData) {α : ℝ} (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos α else Real.cos α) :
    d.b=Real.arccos (|2*Real.cos α|-1) := by
  have hd : 0<Real.cos d.alpha := Real.cos_pos_of_mem_Ioo ⟨by linarith [d.alpha_pos,Real.pi_pos],d.alpha_lt⟩
  have ha : |Real.cos α|=Real.cos d.alpha := by
    cases negative <;> simp only [Bool.false_eq_true,↓reduceIte] at hcos
    · rw [←hcos,abs_of_pos hd]
    · rw [abs_of_neg (by linarith : Real.cos α<0)]
      exact hcos.symm
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),ha,←d.angle_relation]
  exact (Real.arccos_cos d.b_pos.le d.b_lt.le).symm

/-- The actual localized torus integrals at every regular lower-order
center have bounded derivatives; no phase-gap or continuation premise remains. -/
theorem lower_localized_signed_bound {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a))
    (n : ℕ) (hodd : Odd (n+1)) (hnp : n+1<p) {g τ : ℝ} (hg : 0<g) (hτ : 0≤τ)
    (l : ℤ) (hl : l∈regularSignedMeanIndices d B negative (n+1) g) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,Continuous χ →
      (∀ θ,χ θ≠0 → ‖θ-(fun _ => signedEqualityMean negative (n+1) l)‖<R) →
      ∀ W : (Fin (n+1) → ℝ) → ℂ,Continuous W → ∀ j : ℕ,
      ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖(deriv^[j] (localizedSignedLiftedIntegral n negative d B τ χ W)) (radialParameter d.alpha ε)‖≤C := by
  have hmean := (Finset.mem_filter.mp hl).2
  obtain ⟨β,hβ,hβπ,hrel⟩ := right_mean_regular_phase d (by positivity : 0<g/4)
    (by linarith [B.delta_b,d.b_pos] : B.delta<d.b) hmean
  have hlevel : Real.cos (signedEqualityMean negative (n+1) l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a) := by
    cases negative <;> simp only [Bool.false_eq_true,↓reduceIte] at hcos ⊢ <;> linarith
  have hgap := lower_signed_equality_product_gap hp hp5 ha (by omega : 0<n+1) hodd hnp negative l β hlevel
  exact localized_signed_integral_derivatives_bounded n negative d B hτ l (by positivity : 0<g/4)
    hmean β hβ hβπ hrel hgap

theorem first_other_localized_signed_bound {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (negative : Bool)
    (hcos : Real.cos d.alpha=if negative then -Real.cos (angle p a) else Real.cos (angle p a))
    (n : ℕ) (hn : n+1=p) {g τ : ℝ} (hg : 0<g) (hτ : 0≤τ)
    (l : ℤ) (hl : l∈regularSignedMeanIndices d B negative (n+1) g)
    (hother : signedEqualityMean negative (n+1) l≠ -d.alpha) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,Continuous χ →
      (∀ θ,χ θ≠0 → ‖θ-(fun _ => signedEqualityMean negative (n+1) l)‖<R) →
      ∀ W : (Fin (n+1) → ℝ) → ℂ,Continuous W → ∀ j : ℕ,
      ∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ‖(deriv^[j] (localizedSignedLiftedIntegral n negative d B τ χ W)) (radialParameter d.alpha ε)‖≤C := by
  have hmean := (Finset.mem_filter.mp hl).2
  obtain ⟨β,hβ,hβπ,hrel⟩ := right_mean_regular_phase d (by positivity : 0<g/4)
    (by linarith [B.delta_b,d.b_pos] : B.delta<d.b) hmean
  have hlevel : Real.cos (signedEqualityMean negative (n+1) l)+Real.cos β =
      if negative then -(2*Real.cos (angle p a)) else 2*Real.cos (angle p a) := by
    cases negative <;> simp only [Bool.false_eq_true,↓reduceIte] at hcos ⊢ <;> linarith
  have hgap : 1-Physical.constraintSign negative*(Complex.exp (-(β:ℂ)*Complex.I))^(n+1)≠0 := by
    intro hz
    apply hother
    rw [hn] at hz hlevel ⊢
    apply first_signed_right_equality_unique hp hp5 ha negative l β d B hcos hlevel _ (sub_eq_zero.mp hz).symm
    rw [←hn]
    exact ⟨by linarith [hmean.1,d.b_lt,B.delta_pos],hmean.2⟩
  exact localized_signed_integral_derivatives_bounded n negative d B hτ l (by positivity : 0<g/4)
    hmean β hβ hβπ hrel hgap

end
end IsingBulk.HT22.Geometry

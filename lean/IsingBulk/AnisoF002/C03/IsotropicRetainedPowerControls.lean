import IsingBulk.AnisoF002.C03.IsotropicTransportDensity
import IsingBulk.AnisoF002.C03.IsotropicActualVelocityBuffer

/-!
# Actual retained collision powers for integrated transport

At a fixed particle number the complete normalized amplitude, its
successor, its first real jet, and its angular flux velocity have one
common geometric buffer. All constants precede the radial parameter
and the real angular tuple. These are the bounds used to remove only
the flux value at the single total coincidence.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators ContDiff

theorem isotropicShellDelta_right_uniform {N : ℕ} (b β ε r : ℝ) (θ : Fin N → ℝ)
    (hb : b < Real.pi) (hβ : β ≤ 1) (hε : 0 < ε) (hr : 0 < r)
    (hθ : ∀ i, θ i ∈ Icc (-b - β) β) (hlow : ∃ i j, r ≤ |θ i - θ j|) :
    isotropicShellDelta b ε r θ ≤ Real.sqrt (Real.pi + 2) := by
  have hT : 0 < isotropicShellT b ε r θ := by
    dsimp [isotropicShellT]
    positivity
  have ht : 0 < Real.sqrt (isotropicShellT b ε r θ) := Real.sqrt_pos.mpr hT
  have hrT : r ≤ isotropicShellT b ε r θ := by
    dsimp [isotropicShellT]
    linarith only [abs_nonneg (angularMean (fun i => θ i + b)), hε]
  have hrmax : r ≤ Real.pi + 2 := by
    obtain ⟨i, j, hij⟩ := hlow
    have hh : |θ i - θ j| ≤ b + 2 * β := abs_le.mpr
      ⟨by linarith [(hθ i).1, (hθ j).2], by linarith [(hθ i).2, (hθ j).1]⟩
    linarith
  apply le_trans (b := Real.sqrt r) _ (Real.sqrt_le_sqrt hrmax)
  apply (div_le_iff₀ ht).mpr
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrT) (Real.sqrt_nonneg r)
  simpa only [Real.mul_self_sqrt hr.le] using hh

theorem exists_actual_retained_power_controls_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ j : ℕ, 2 * j + 2 ≤ 2 * R.card → ∃ A V : ℝ, 0 < A ∧ 0 < V ∧
      ∀ (g : (Fin N → ℝ) → ℂ) (Cg : ℝ), 0 ≤ Cg → ContDiff ℝ ∞ g →
        FiniteJetControl (j + 1) g Cg →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - β) β) →
      ∀ r : ℝ, 0 < r → (∀ i l, |θ i - θ l| ≤ 2 * r) → (∃ i l, r ≤ |θ i - θ l|) →
        let x := (isotropicRadialParameter α ε, θ)
        let Δ := isotropicShellDelta b ε r θ
        let d := 2 * R.card - 2 * j
        Δ ≤ Real.sqrt (Real.pi + 2) ∧
        ‖actualTransportDescendant η τ ξ
          (actualInitialAmplitude η τ ξ (fun y => g y.2)) j x‖ ≤ A * Cg * Δ ^ d ∧
        ‖actualTransportDescendant η τ ξ
          (actualInitialAmplitude η τ ξ (fun y => g y.2)) (j + 1) x‖ ≤ A * Cg * Δ ^ (d - 2) ∧
        ‖fderiv ℝ (actualTransportDescendant η τ ξ
          (actualInitialAmplitude η τ ξ (fun y => g y.2)) j) x‖ ≤
          A * (1 + ‖fderiv ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ)) x‖) * Cg * Δ ^ (d - 1) ∧
        ∀ i, ‖actualCovarianceAngularVelocity η τ ξ i x‖ ≤ V / Δ := by
  obtain ⟨β₀, hβ₀, hβ₀1, hvalue⟩ := exists_actual_normalized_cutoff_descendant_buffer α b hα hb hpoint
  obtain ⟨β₁, hβ₁, _, hjet⟩ := exists_actual_cutoff_first_real_jet_buffer α b hα hb hpoint
  obtain ⟨β₂, hβ₂, _, hvelocity⟩ := exists_actual_velocity_shell_buffer α b hα hb hpoint
  let β := min β₀ (min β₁ β₂)
  have hβ : 0 < β := lt_min hβ₀ (lt_min hβ₁ hβ₂)
  have hb0 : β ≤ β₀ := min_le_left _ _
  have hb1 : β ≤ β₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb2 : β ≤ β₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hβ1' : β ≤ 1 := hb0.trans hβ₀1
  refine ⟨β, hβ, hβ1', ?_⟩
  intro η hη hwidth
  obtain ⟨δ₀, κ, C, M, hδ₀, _, hκ, hC, hM, hvalues⟩ := hvalue η hη hwidth
  obtain ⟨δ₁, hδ₁, _, hjets⟩ := hjet η hη hwidth
  obtain ⟨δ₂, V₀, hδ₂, _, hV₀, hvel⟩ := hvelocity η hη hwidth
  let δ := min β (min δ₀ (min δ₁ δ₂))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hd0 : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : δ ≤ δ₁ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : δ ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN R hR j hjR
  obtain ⟨Cj, hCj, hvj⟩ := hvalues j
  obtain ⟨Cnext, hCnext, hvnext⟩ := hvalues (j + 1)
  obtain ⟨Aj, hAj, hjets'⟩ := hjets N hN R hR j
  let L (k : ℕ) (ck : ℝ) :=
    (ck * (N : ℝ) ^ ((7 + 3 * k) * k) * C ^ N * M ^ R.card *
      Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)) /
      ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1))
  let A := max 1 (max (L j Cj) (max (L (j + 1) Cnext) Aj))
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hA0 : L j Cj ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hA1 : L (j + 1) Cnext ≤ A := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hA2 : Aj ≤ A := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨A, V₀ * (N : ℝ) ^ 3, hA, by positivity, ?_⟩
  intro g Cg hCg hg hgj ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hlow
  dsimp only
  let Δ := isotropicShellDelta b ε r θ
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  have hθ0 : ∀ i, θ i ∈ Icc (-b - β₀) β₀ :=
    fun i => ⟨by linarith [(hθ i).1], (hθ i).2.trans hb0⟩
  have hθ1 : ∀ i, θ i ∈ Icc (-b - β₁) β₁ :=
    fun i => ⟨by linarith [(hθ i).1], (hθ i).2.trans hb1⟩
  have hθ2 : ∀ i, θ i ∈ Icc (-b - β₂) β₂ :=
    fun i => ⟨by linarith [(hθ i).1], (hθ i).2.trans hb2⟩
  have hv₀ := hvj N hN R hR g Cg hCg hg (hgj.mono_order (by omega)) ε hε
    (hεδ.trans hd0) τ ξ ⟨hτ.1, hτ.2.trans hd0⟩ hξ θ hθ0 r hr hdiam hlow
  have hv₁ := hvnext N hN R hR g Cg hCg hg hgj ε hε
    (hεδ.trans hd0) τ ξ ⟨hτ.1, hτ.2.trans hd0⟩ hξ θ hθ0 r hr hdiam hlow
  have hv₂ := hjets' g Cg hCg hg hgj ε hε (hεδ.trans hd1) τ ξ
    ⟨hτ.1, hτ.2.trans hd1⟩ hξ θ hθ1 r hr hdiam hlow
  have he₀ : 2 * j ≤ 2 * R.card := by omega
  have he₁ : 2 * (j + 1) ≤ 2 * R.card := by omega
  have he₂ : 2 * j + 1 ≤ 2 * R.card := by omega
  refine ⟨isotropicShellDelta_right_uniform b β ε r θ hb.2 hβ1' hε hr hθ hlow, ?_, ?_, ?_, ?_⟩
  · apply hv₀.trans
    calc
      _ = L j Cj * Cg * (Δ ^ (2 * R.card) / Δ ^ (2 * j)) := by dsimp [L, Δ]; ring
      _ = L j Cj * Cg * Δ ^ (2 * R.card - 2 * j) := by rw [retained_power_division hΔ.ne' he₀]
      _ ≤ _ := by gcongr
  · apply hv₁.trans
    calc
      _ = L (j + 1) Cnext * Cg * (Δ ^ (2 * R.card) / Δ ^ (2 * (j + 1))) := by dsimp [L, Δ]; ring
      _ = L (j + 1) Cnext * Cg * Δ ^ (2 * R.card - 2 * j - 2) := by
        rw [retained_power_division hΔ.ne' he₁]
        congr 2
      _ ≤ _ := by gcongr
  · apply hv₂.trans
    calc
      _ = Aj * (1 + ‖fderiv ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ))
          (isotropicRadialParameter α ε, θ)‖) * Cg * (Δ ^ (2 * R.card) / Δ ^ (2 * j + 1)) := by
        dsimp [Δ]
        ring
      _ = Aj * (1 + ‖fderiv ℝ (regularJointMap (actualPhysicalCoordinate η τ ξ))
          (isotropicRadialParameter α ε, θ)‖) * Cg * Δ ^ (2 * R.card - 2 * j - 1) := by
        rw [retained_power_division hΔ.ne' he₂]
        congr 2
      _ ≤ _ := by gcongr
  · exact hvel N hN ε hε (hεδ.trans hd2) τ ξ ⟨hτ.1, hτ.2.trans hd2⟩ hξ θ hθ2 r hr hdiam hlow

end
end IsingBulk.AnisoF002.Isotropic

import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferPositiveIntegral
import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferNegativeIntegral
import IsingBulk.AnisoF002.C03.IsotropicActualFullFiberCoarea

/-!
# The complete signed physical fiber integral with independent angular and time buffers
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem exists_actual_full_extreme_fiber_integral_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r γ A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ fullExtremeFiber θ i j b β r →
        (∫ t in A..B, actualExtremeFiberDensity (isotropicRadialParameter α ε) η τ ξ γ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨βP, hβP, hβP1, hPdata⟩ :=
    exists_actual_positive_extreme_integral_buffer α b hα hb hpoint
  obtain ⟨βN, hβN, _, hNdata⟩ :=
    exists_actual_negative_extreme_integral_buffer α b hα hb hpoint
  let β := min βP βN
  have hβ : 0 < β := lt_min hβP hβN
  have hβP' : β ≤ βP := min_le_left _ _
  have hβN' : β ≤ βN := min_le_right _ _
  have hβ1 : β ≤ 1 := hβP'.trans hβP1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δP, CP, hδP, _, hCP, hpositive⟩ := hPdata η hη hwidth
  obtain ⟨CN, hCN, hnegative⟩ := hNdata η hη hwidth
  let δ := min δP β
  let C := CP + CN
  have hδ : 0 < δ := lt_min hδP hβ
  have hδP' : δ ≤ δP := min_le_left _ _
  have hδβ : δ ≤ β := min_le_right _ _
  have hδN' : δ ≤ βN := hδβ.trans hβN'
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, C, hδ, hδβ, add_pos hCP hCN, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j r γ A B hr hAB hfiber
  let s := isotropicRadialParameter α ε
  let H := Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r * (1 + |Real.log ε|)
  let f := actualExtremeFiberDensity s η τ ξ γ θ i j
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hij : i ≠ j := by
    intro he
    have hh := (hfiber (left_mem_Icc.mpr hAB)).2.2.2.1
    rw [he, sub_self] at hh
    linarith only [hr, hh]
  have hpos (a c : ℝ) (hac : a ≤ c) (hsub : Icc a c ⊆ Icc A B)
      (hmin : ∀ t ∈ Icc a c, 0 ≤ constrainedAngleLine θ i j t i + b) :
      (∫ t in a..c, f t) ≤ CP * N * H := by
    have hproper : Icc a c ⊆ positiveExtremeFiber θ i j b βP r := by
      intro t ht
      have hf := hfiber (hsub ht)
      refine ⟨?_, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
      intro k
      exact ⟨by linarith only [hmin t ht, hf.2.1 k], (hf.1 k).2.trans hβP'⟩
    have hh := hpositive N hN ε hε (hεδ.trans hδP') τ ξ ⟨hτ.1, hτ.2.trans hδP'⟩ hξ
      θ i j r γ a c hr hac hproper
    exact hh.trans_eq (by dsimp [H]; ring)
  have hneg (a c : ℝ) (hac : a ≤ c) (hsub : Icc a c ⊆ Icc A B)
      (hmin : ∀ t ∈ Icc a c, constrainedAngleLine θ i j t i + b ≤ 0) :
      (∫ t in a..c, f t) ≤ CN * H := by
    have hproper : Icc a c ⊆ negativeExtremeFiber θ i j b βN r := by
      intro t ht
      have hf := hfiber (hsub ht)
      refine ⟨⟨?_, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩, hmin t ht⟩
      intro k
      exact ⟨by linarith only [(hf.1 k).1, hβN'], (hf.1 k).2.trans hβN'⟩
    have hh := hnegative N hN ε hε (hεδ.trans hδN') τ ξ ⟨hτ.1, hτ.2.trans hδN'⟩ hξ
      θ i j r γ a c hr hac hproper
    exact hh.trans_eq (by dsimp [H]; ring)
  have hNcost : CN * H ≤ CN * N * H := by
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg hCN.le hH)
    nlinarith only [hh]
  have hCPcost : 0 ≤ CP * N * H := mul_nonneg (mul_nonneg hCP.le hnpos.le) hH
  have hCNcost : 0 ≤ CN * N * H := mul_nonneg (mul_nonneg hCN.le hnpos.le) hH
  have hjoin : (∫ t in A..B, f t) ≤ (CP + CN) * N * H := by
    let z := -b - θ i
    by_cases hzA : z ≤ A
    · have hh := hpos A B hAB (fun _ ht => ht) (fun t ht => by
        rw [constrainedAngleLine_first θ i j hij t]
        dsimp [z] at hzA
        linarith only [hzA, ht.1])
      nlinarith only [hh, hCNcost]
    · by_cases hBz : B ≤ z
      · have hh := hneg A B hAB (fun _ ht => ht) (fun t ht => by
          rw [constrainedAngleLine_first θ i j hij t]
          dsimp [z] at hBz
          linarith only [hBz, ht.2])
        nlinarith only [hh, hNcost, hCPcost]
      · have hAz : A ≤ z := (lt_of_not_ge hzA).le
        have hzB : z ≤ B := (lt_of_not_ge hBz).le
        have hleft := hneg A z hAz (fun _ ht => ⟨ht.1, ht.2.trans hzB⟩) (fun t ht => by
          rw [constrainedAngleLine_first θ i j hij t]
          dsimp [z] at ht
          linarith only [ht.2])
        have hright := hpos z B hzB (fun _ ht => ⟨hAz.trans ht.1, ht.2⟩) (fun t ht => by
          rw [constrainedAngleLine_first θ i j hij t]
          dsimp [z] at ht
          linarith only [ht.1])
        have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
        have hcont : Continuous f := actualExtremeFiberDensity_continuous s hs η τ ξ γ hη hτ.1 hξ.1 θ i j
        rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable A z)
          (hcont.intervalIntegrable z B)]
        nlinarith only [hleft, hright, hNcost]
  exact hjoin.trans_eq (by dsimp [C, H]; ring)

theorem exists_actual_signed_full_extreme_fiber_integral_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ fullExtremeFiber θ i j b β r →
        ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ t in A..B, actualSignedExtremeFiberDensity (isotropicRadialParameter α ε) σ η τ ξ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_full_extreme_fiber_integral_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, hδ, hδβ, hC, hbound⟩ := hdata η hη hwidth
  refine ⟨δ, C, hδ, hδβ, hC, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j r A B hr hAB hfiber σ hσ
  obtain ⟨γ, hγ⟩ := exists_actual_signed_phase_shift (isotropicRadialParameter α ε) σ hσ η τ ξ θ i j
  rw [← funext hγ]
  exact hbound N hN ε hε hεδ τ ξ hτ hξ θ i j r γ A B hr hAB hfiber

end IsingBulk.AnisoF002.Isotropic

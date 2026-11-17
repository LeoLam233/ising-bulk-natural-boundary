import IsingBulk.AnisoF002.C03.IsotropicActualNegativeCoarea

/-!
# The complete actual extreme-coordinate fiber integral

The full right rectangle includes both signs of the minimum. Its true
constraint fiber is one compact interval. Splitting that interval at
the actual zero of the minimum combines the positive phase coarea and
negative attenuation bounds without a differentiated diameter cutoff.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

def fullExtremeFiber {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (b δ r : ℝ) : Set ℝ :=
  positiveExtremeFiber θ i j (b + δ) δ r

theorem fullExtremeFiber_eq_interval {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N)
    (hij : i ≠ j) (b δ r : ℝ) (hne : (fullExtremeFiber θ i j b δ r).Nonempty) :
    ∃ A B : ℝ, A ≤ B ∧ fullExtremeFiber θ i j b δ r = Icc A B :=
  positiveExtremeFiber_eq_interval θ i j hij (b + δ) δ r hne

theorem exists_actual_full_extreme_fiber_integral (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r γ A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ fullExtremeFiber θ i j b δ r →
        (∫ t in A..B, actualExtremeFiberDensity (isotropicRadialParameter α ε) η τ ξ γ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨δP, CP, hδP, hδP1, hCP, hpositive⟩ :=
    exists_actual_positive_extreme_integral α b η hα hb hpoint hη hwidth
  obtain ⟨δN, CN, hδN, _, hCN, hnegative⟩ :=
    exists_actual_negative_extreme_integral α b η hα hb hpoint hη hwidth
  let δ := min δP δN
  let C := CP + CN
  have hδ : 0 < δ := lt_min hδP hδN
  have hδP' : δ ≤ δP := min_le_left _ _
  have hδN' : δ ≤ δN := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδP'.trans hδP1
  refine ⟨δ, C, hδ, hδ1, add_pos hCP hCN, ?_⟩
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
    have hproper : Icc a c ⊆ positiveExtremeFiber θ i j b δP r := by
      intro t ht
      have hf := hfiber (hsub ht)
      refine ⟨?_, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
      intro k
      exact ⟨by linarith only [hmin t ht, hf.2.1 k], (hf.1 k).2.trans hδP'⟩
    have hh := hpositive N hN ε hε (hεδ.trans hδP') τ ξ ⟨hτ.1, hτ.2.trans hδP'⟩ hξ
      θ i j r γ a c hr hac hproper
    exact hh.trans_eq (by dsimp [H]; ring)
  have hneg (a c : ℝ) (hac : a ≤ c) (hsub : Icc a c ⊆ Icc A B)
      (hmin : ∀ t ∈ Icc a c, constrainedAngleLine θ i j t i + b ≤ 0) :
      (∫ t in a..c, f t) ≤ CN * H := by
    have hproper : Icc a c ⊆ negativeExtremeFiber θ i j b δN r := by
      intro t ht
      have hf := hfiber (hsub ht)
      refine ⟨⟨?_, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩, hmin t ht⟩
      intro k
      exact ⟨by linarith only [(hf.1 k).1, hδN'], (hf.1 k).2.trans hδN'⟩
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

/-- Complete physical extreme-fiber integral for both root-product
signs, over the entire enlarged right rectangle. -/
theorem exists_actual_signed_full_extreme_fiber_integral (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ) (i j : Fin N) (r A B : ℝ), 0 < r → A ≤ B →
        Icc A B ⊆ fullExtremeFiber θ i j b δ r →
        ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ t in A..B, actualSignedExtremeFiberDensity (isotropicRadialParameter α ε) σ η τ ξ θ i j t) ≤
          C * N * Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) / r *
            (1 + |Real.log ε|) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hbound⟩ :=
    exists_actual_full_extreme_fiber_integral α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ i j r A B hr hAB hfiber σ hσ
  obtain ⟨γ, hγ⟩ := exists_actual_signed_phase_shift (isotropicRadialParameter α ε) σ hσ η τ ξ θ i j
  rw [← funext hγ]
  exact hbound N hN ε hε hεδ τ ξ hτ hξ θ i j r γ A B hr hAB hfiber

end IsingBulk.AnisoF002.Isotropic

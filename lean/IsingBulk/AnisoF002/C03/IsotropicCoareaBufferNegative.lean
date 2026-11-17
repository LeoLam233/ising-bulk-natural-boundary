import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferWeights
import IsingBulk.AnisoF002.C03.IsotropicActualNegativeKernel

/-!
# Actual negative extreme-kernel bound on a fixed geometric buffer
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric Filter MeasureTheory

theorem exists_actual_negative_extreme_kernel_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b - δ) δ) →
      ∀ (i j : Fin N) (γ : ℝ), θ i + b ≤ 0 →
        ‖(1 + actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i) *
            (1 + actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ j)‖ /
          ‖1 - Complex.exp (-Complex.I *
            (actualTotalPhase η τ ξ (isotropicRadialParameter α ε, θ) - (γ : ℂ)))‖ ≤
          C / ((|θ i + b| + ε) * Real.sqrt (|θ j + b| + ε)) := by
  obtain ⟨rB, cB, hrB, hrB1, hcB, hbranch⟩ :=
    exists_isotropic_negative_branch_phase_attenuation α b hα hb hpoint
  obtain ⟨δW, hδW, _, hweightData⟩ :=
    exists_actual_whole_arc_jacobian_weight_buffer α b hα hb hpoint
  have hsinb := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let δ := min rB (min δW (Real.sin b / 4))
  let c := min cB (1 / 2)
  have hδ : 0 < δ := lt_min hrB (lt_min hδW (div_pos hsinb (by norm_num)))
  have hδB : δ ≤ rB := min_le_left _ _
  have hδW' : δ ≤ δW := (min_le_right _ _).trans (min_le_left _ _)
  have hδsin : δ ≤ Real.sin b / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (by linarith only [hsinb])
  have hδ1 : δ ≤ 1 := hδB.trans hrB1
  have hc : 0 < c := lt_min hcB (by norm_num)
  have hccB : c ≤ cB := min_le_left _ _
  have hc1 : c ≤ 1 / 2 := min_le_right _ _
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη hwidth
  obtain ⟨W, hW, hweight⟩ := hweightData η hη hwidth
  let C := W ^ 2 * (2 / c)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ i j γ hi
  let s := isotropicRadialParameter α ε
  let u := θ i + b
  let h := ξ * τ * actualUpperOccupancy η θ
  let a := |u| + ε
  let d := |θ j + b| + ε
  let z := actualTotalPhase η τ ξ (s, θ) - (γ : ℂ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hu : u ∈ Icc (-δ) 0 := ⟨by dsimp [u]; linarith only [(hθ i).1], hi⟩
  have huabs : |u| ≤ δ := by rw [abs_of_nonpos hu.2]; linarith only [hu.1]
  have hh : h ∈ Icc 0 δ := actualCommonBranchDepth_mem_Icc hN η τ ξ δ hτ hξ θ
  have hident : actualPhysicalPhase η τ ξ (s, θ) i =
      upperPhysicalPhase (isotropicBranchDispersion α b ε u h) := by
    rw [actualPhysicalPhase, actualHomotopyAngle_eq_fixedOccupancy]
    dsimp only [Prod.fst, Prod.snd]
    have he : θ i = -b + u := by dsimp [u]; ring
    nth_rw 1 [he]
    rw [fixedOccupancyAngle_geometric_branch b η (ξ * τ) _ _ u hη hwidth (huabs.trans hδsin)]
    rfl
  have hlocal : cB * Real.sqrt (a + h) ≤ -(actualPhysicalPhase η τ ξ (s, θ) i).im := by
    rw [hident]
    exact hbranch ε hε (hεδ.trans hδB) u h
      ⟨by linarith only [hu.1, hδB], hu.2⟩ ⟨hh.1, hh.2.trans hδB⟩
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hsum := actualTotalPhase_attenuation_ge_individual s hs η τ ξ hη hτ.1 hξ.1 θ i
  have hatten : c * Real.sqrt a ≤ -z.im := by
    have hroot := Real.sqrt_le_sqrt (show a ≤ a + h by linarith only [hh.1])
    have hm := mul_le_mul hccB hroot (Real.sqrt_nonneg a) hcB.le
    have he : z.im = (actualTotalPhase η τ ξ (s, θ)).im := by simp only [z, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [he]
    exact hm.trans (hlocal.trans hsum)
  have ha2 : a ≤ 2 := by dsimp [a]; linarith only [huabs, hεδ, hδ1]
  have hroot2 : Real.sqrt a ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith only [ha2]⟩
  have ha₀1 : c * Real.sqrt a ≤ 1 := by
    have hh' := mul_le_mul hc1 hroot2 (Real.sqrt_nonneg a) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at hh'
    exact hh'
  have hkernel : 1 / ‖1 - Complex.exp (-Complex.I * z)‖ ≤ (2 / c) / Real.sqrt a := by
    have hh' := phase_denominator_inverse_of_lower_attenuation z (c * Real.sqrt a)
      (mul_pos hc (Real.sqrt_pos.mpr ha)) ha₀1 hatten
    simpa only [div_div] using hh'
  have hθW : ∀ k, θ k ∈ Icc (-Real.pi - δW) δW :=
    fun k => ⟨by linarith only [(hθ k).1, hb.2, hδW'], (hθ k).2.trans hδW'⟩
  have hwi := hweight N hN ε hε (hεδ.trans hδW') τ ξ ⟨hτ.1, hτ.2.trans hδW'⟩ hξ θ hθW i
  have hwj := hweight N hN ε hε (hεδ.trans hδW') τ ξ ⟨hτ.1, hτ.2.trans hδW'⟩ hξ θ hθW j
  have hpair : ‖(1 + actualPhaseSlope s η τ ξ θ i) * (1 + actualPhaseSlope s η τ ξ θ j)‖ ≤
      (W / Real.sqrt a) * (W / Real.sqrt d) := by
    rw [norm_mul]
    exact mul_le_mul hwi hwj (norm_nonneg _) (by positivity)
  calc
    _ = ‖(1 + actualPhaseSlope s η τ ξ θ i) * (1 + actualPhaseSlope s η τ ξ θ j)‖ *
        (1 / ‖1 - Complex.exp (-Complex.I * z)‖) := by ring
    _ ≤ ((W / Real.sqrt a) * (W / Real.sqrt d)) * ((2 / c) / Real.sqrt a) :=
      mul_le_mul hpair hkernel (by positivity) (by positivity)
    _ = C / (a * Real.sqrt d) := by
      dsimp [C]
      calc
        _ = (W ^ 2 * (2 / c)) / (Real.sqrt a ^ 2 * Real.sqrt d) := by ring
        _ = _ := by rw [Real.sq_sqrt ha.le]

end IsingBulk.AnisoF002.Isotropic

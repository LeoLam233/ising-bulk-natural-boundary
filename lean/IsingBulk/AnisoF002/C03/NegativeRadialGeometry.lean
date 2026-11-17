import IsingBulk.AnisoF002.C03.NegativeTailLogAbsorption

/-! # Actual radial parameter, fixed-ball geometry, and full density bounds -/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

set_option maxHeartbeats 1000000 in
theorem radial_parameter_comparison {N τ a Q : ℝ}
    (hN : 0 < N) (hτ : 0 < τ) (hQ : 0 ≤ Q)
    (hτlo : 2 / N ^ 2 ≤ τ) (hτhi : τ ≤ Real.pi ^ 2 / (2 * N ^ 2))
    (halo : (1 / 2 : ℝ) ≤ a) (hahi : a ≤ 2) :
    let x := a * Q / (2 * N * τ)
    0 ≤ x ∧ x ≤ N * Q ∧ N * Q ≤ 2 * Real.pi ^ 2 * x := by
  dsimp only
  have ha : 0 < a := by linarith
  have hlo : 2 ≤ τ * N ^ 2 := (div_le_iff₀ (sq_pos_of_pos hN)).mp hτlo
  have hhi : τ * (2 * N ^ 2) ≤ Real.pi ^ 2 :=
    (le_div_iff₀ (by positivity : 0 < 2 * N ^ 2)).mp hτhi
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2 * N * τ)).mpr
    have hh : a ≤ 2 * τ * N ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh hQ
    nlinarith
  · have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hm := mul_le_mul_of_nonneg_right hhi hQ
    have ha' := mul_le_mul_of_nonneg_right halo (by positivity : 0 ≤ 2 * Real.pi ^ 2 * Q)
    have ht : N * Q * (2 * N * τ) ≤ 2 * Real.pi ^ 2 * (a * Q) := by nlinarith
    calc
      _ ≤ (2 * Real.pi ^ 2 * (a * Q)) / (2 * N * τ) :=
        (le_div_iff₀ (by positivity)).mpr ht
      _ = _ := by ring

theorem radial_density_bound {N τ a Q K : ℝ} {ell : ℂ}
    (hN : 0 < N) (hτ : 0 < τ) (hQ : 0 ≤ Q)
    (hτlo : 2 / N ^ 2 ≤ τ) (hτhi : τ ≤ Real.pi ^ 2 / (2 * N ^ 2))
    (halo : (1 / 2 : ℝ) ≤ a) (hahi : a ≤ 2) (hK : 0 ≤ K)
    (hell : ‖ell‖ ≤ K * (Real.sqrt (N * Q) + N * Q)) :
    let x := a * Q / (2 * N * τ)
    ‖ell‖ ≤ (K * (1 + 2 * Real.pi ^ 2)) * (Real.sqrt x + x) := by
  let x := a * Q / (2 * N * τ)
  obtain ⟨hx, _, hu⟩ := radial_parameter_comparison hN hτ hQ hτlo hτhi halo hahi
  change 0 ≤ x at hx
  change N * Q ≤ 2 * Real.pi ^ 2 * x at hu
  have hc : Real.sqrt (2 * Real.pi ^ 2) ≤ 1 + 2 * Real.pi ^ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi ^ 2 by positivity)]
  have hr : Real.sqrt (N * Q) ≤ (1 + 2 * Real.pi ^ 2) * Real.sqrt x := by
    calc
      _ ≤ Real.sqrt (2 * Real.pi ^ 2 * x) := Real.sqrt_le_sqrt hu
      _ = Real.sqrt (2 * Real.pi ^ 2) * Real.sqrt x := Real.sqrt_mul (by positivity) _
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg x)
  have hu' : N * Q ≤ (1 + 2 * Real.pi ^ 2) * x := by nlinarith
  calc
    _ ≤ K * (Real.sqrt (N * Q) + N * Q) := hell
    _ ≤ K * ((1 + 2 * Real.pi ^ 2) * Real.sqrt x + (1 + 2 * Real.pi ^ 2) * x) :=
      mul_le_mul_of_nonneg_left (add_le_add hr hu') hK
    _ = _ := by ring

theorem radial_outer_region {N k τ a Q A : ℝ}
    (hN : 1 ≤ N) (hk : 0 < k) (hτ : 0 < τ) (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hτlo : 2 / N ^ 2 ≤ τ) (hτhi : τ ≤ Real.pi ^ 2 / (2 * N ^ 2))
    (halo : (1 / 2 : ℝ) ≤ a) (hahi : a ≤ 2)
    (hA : 2 * Real.pi ^ 2 ≤ A) (houter : A * N / k ≤ Q) :
    let x := a * Q / (2 * N * τ)
    0 < x ∧ N ^ 2 ≤ k * x ∧ x ≤ N := by
  have hN0 : 0 < N := by linarith
  have hA0 : 0 < A := (by positivity : 0 < 2 * Real.pi ^ 2).trans_le hA
  have hQ0 : 0 < Q := (by positivity : 0 < A * N / k).trans_le houter
  obtain ⟨hx, hxu, hux⟩ := radial_parameter_comparison hN0 hτ hQ hτlo hτhi halo hahi
  dsimp only
  refine ⟨by positivity, ?_, hxu.trans (by nlinarith)⟩
  have hl : A * N ≤ Q * k := (div_le_iff₀ hk).mp houter
  have hln := mul_le_mul_of_nonneg_right hl hN0.le
  have huxk := mul_le_mul_of_nonneg_right hux hk.le
  have hAn := mul_le_mul_of_nonneg_right hA (sq_nonneg N)
  have hp : 0 < 2 * Real.pi ^ 2 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
theorem higher_pole_error_small_strong (n : ℕ) (hn : 0 < n) (v : Fin n → ℂ)
    {K σ : ℝ} (hK : 0 ≤ K) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hKσ : 768 * K * σ ≤ 1) (hQ : displacementSquare n v < σ ^ 2)
    {T T₀ : ℂ}
    (herr : ‖T - T₀‖ ≤ K / (n : ℝ) *
      ((∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
        displacementSquare n v ^ 2 / (n : ℝ))) :
    ‖T - T₀‖ ≤ displacementSquare n v / (256 * (n : ℝ)) := by
  have he : ‖(16 : ℂ) * T - (16 : ℂ) * T₀‖ = 16 * ‖T - T₀‖ := by
    rw [← mul_sub, norm_mul]
    norm_num
  have hb : ‖(16 : ℂ) * T - (16 : ℂ) * T₀‖ ≤ (16 * K) / (n : ℝ) *
      ((∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
        displacementSquare n v ^ 2 / (n : ℝ)) := by
    rw [he]
    convert mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 16) using 1
    ring
  have hs := higher_pole_error_small n hn v (by positivity : 0 ≤ 16 * K) hσ hσ1
    (by nlinarith : 48 * (16 * K) * σ ≤ 1) hQ hb
  rw [he] at hs
  calc
    _ = (16 * ‖T - T₀‖) / 16 := by ring
    _ ≤ (displacementSquare n v / (16 * (n : ℝ))) / 16 :=
      div_le_div_of_nonneg_right hs (by norm_num)
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT

import IsingBulk.HT22.Near.QuadraticDyadicSum

namespace IsingBulk.HT22.Near
noncomputable section
open scoped BigOperators ENNReal

/-- Raw small-scale mass, also used to send the full-equality puncture to zero
at fixed particle count and fixed positive epsilon. -/
theorem near_raw_dyadic_ennreal_sum (μ : ℝ) {ε δ K H : ℝ} (hε : 0≤ε)
    (hδ : 0≤δ) (hK : 0≤K) (hH : 0≤H) {p : ℕ} (hp : 1≤p)
    (F : ℕ → ℝ≥0∞)
    (hF : ∀ n,dyadicScale μ ε n≤δ →
      F n≤ENNReal.ofReal (K*dyadicScale μ ε n^p*H)) :
    (∑' n,if dyadicScale μ ε n≤δ then F n else 0)≤
      ENNReal.ofReal (4*K*δ^p*H) := by
  classical
  obtain ⟨hs,hb⟩ := dyadic_near_power_sum μ hε hδ hp
  let g := fun n => if dyadicScale μ ε n≤δ then dyadicScale μ ε n^p else 0
  have hg (n) : 0≤g n := by
    dsimp [g]
    split
    · exact pow_nonneg (shellCoordinateScale_pos μ
        (IsingBulk.Preferred22.preferredDyadicRadius_pos n) hε).le _
    · exact le_refl _
  have hpoint (n) : (if dyadicScale μ ε n≤δ then F n else 0)≤ENNReal.ofReal (K*g n*H) := by
    by_cases hn : dyadicScale μ ε n≤δ
    · simpa [g,hn] using hF n hn
    · simp [g,hn]
  calc
    _ ≤ ∑' n,ENNReal.ofReal (K*g n*H) := ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (K*(∑' n,g n)*H) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg hK (hg n)) hH) ((hs.mul_left K).mul_right H),
        tsum_mul_right,tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hK) hH
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hh

theorem near_dyadic_ennreal_sum (μ : ℝ) {ε δ C H : ℝ} (hε : 0≤ε)
    (hδ : 0<δ) (hδ1 : δ≤1) (hC : 0≤C) (hsmall : C*δ≤1/2) (hH : 0≤H)
    {j k p N : ℕ} (hjk : j≤k) (hp : 1≤p)
    (hdegree : (p:ℝ)=(N:ℝ)^2-2*(j:ℝ)-3)
    (F : ℕ → ℝ≥0∞)
    (hF : ∀ n,dyadicScale μ ε n≤δ →
      F n≤ENNReal.ofReal (C^(N^2)*dyadicScale μ ε n^p*H)) :
    (∑' n,if dyadicScale μ ε n≤δ then F n else 0)≤
      ENNReal.ofReal (4*δ^(-2*(k:ℝ)-3)*nearOrderEnvelope N*H) := by
  classical
  obtain ⟨hs,hb⟩ := near_quadratic_dyadic_sum μ hε hδ hδ1 hC hsmall hjk hp hdegree
  let g := fun n => C^(N^2)*(if dyadicScale μ ε n≤δ then dyadicScale μ ε n^p else 0)
  have hg (n) : 0≤g n := by
    dsimp [g]
    split
    · exact mul_nonneg (pow_nonneg hC _) (pow_nonneg
        (shellCoordinateScale_pos μ (IsingBulk.Preferred22.preferredDyadicRadius_pos n) hε).le _)
    · simp
  have hpoint (n) : (if dyadicScale μ ε n≤δ then F n else 0)≤ENNReal.ofReal (g n*H) := by
    by_cases hn : dyadicScale μ ε n≤δ
    · simpa [g,hn] using hF n hn
    · simp [g,hn]
  calc
    _ ≤ ∑' n,ENNReal.ofReal (g n*H) := ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal ((∑' n,g n)*H) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hg n) hH) (hs.mul_right H),tsum_mul_right]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hb hH)

end
end IsingBulk.HT22.Near

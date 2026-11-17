import IsingBulk.AnisoF002.C03.NegativeParticleWindow

/-!
# All resonant middle-particle competitors, in the actual physical window

The consecutive-window proof and full prefix estimate are combined here.
The resulting sum contains every resonant odd population in the physical
middle window except its selected center.  Its length is unrestricted.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem resonantParticleCount_add (p q k : ℕ) :
    resonantParticleCount p (q + k) = resonantParticleCount p q + (2 * p) * k := by
  unfold resonantParticleCount
  ring

theorem resonantParticleCount_sub (p : ℕ) {q k : ℕ} (hk : k ≤ q) :
    resonantParticleCount p q - (2 * p) * k = resonantParticleCount p (q - k) := by
  have hh := resonantParticleCount_add p (q - k) k
  rw [Nat.sub_add_cancel hk] at hh
  omega

theorem exists_complete_middle_model_competitor_bound {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : Odd p) :
    ∃ T : ℝ, 0 < T ∧ ∀ j q : ℕ, 1 ≤ q → T ≤ Real.log j →
      q ∈ resonantMiddleIndices p j →
      |actualModelLog B c s (resonantParticleCount p (q + 1)) j -
        actualModelLog B c s (resonantParticleCount p (q - 1)) j| ≤
          (((2 * p : ℕ) : ℝ)) ^ 2 / 4 * Real.log j →
      let M : ℕ → ℂ := fun n => modelCoefficient n j (B (windingTau n : ℂ))
        (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)
      (∑ k ∈ (resonantMiddleIndices p j).erase q, ‖M (resonantParticleCount p k)‖) ≤
        ‖M (resonantParticleCount p q)‖ *
          (2 * (Real.exp (-((((2 * p : ℕ) : ℝ)) ^ 2 * Real.log j) / 8) /
            (1 - Real.exp (-((((2 * p : ℕ) : ℝ)) ^ 2 * Real.log j) / 8)))) := by
  have hd : Even (2 * p) := even_two_mul p
  have hdpos : 0 < 2 * p := by have := hp.pos; omega
  obtain ⟨T₀, hT₀, hbound⟩ := exists_actual_model_competitor_norm_sum hB hslit c hs (2 * p) hd hdpos
  refine ⟨max T₀ 64, hT₀.trans_le (le_max_left _ _), ?_⟩
  intro j q hq1 hjT hq hcross
  let S := resonantMiddleIndices p j
  have hne : S.Nonempty := ⟨q, hq⟩
  let lo := S.min' hne
  let hi := S.max' hne
  let N := resonantParticleCount p q
  let M : ℕ → ℂ := fun n => modelCoefficient n j (B (windingTau n : ℂ))
    (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)
  change (∑ k ∈ S.erase q, ‖M (resonantParticleCount p k)‖) ≤ ‖M N‖ * _
  have hj64 : 64 ≤ Real.log j := (le_max_right _ _).trans hjT
  have hj1 : 1 ≤ Real.log j := by linarith
  have hlo : lo ≤ q := Finset.min'_le S q hq
  have hhi : q ≤ hi := Finset.le_max' S q hq
  have hmin := (mem_resonantMiddleIndices_iff hp.pos hj1).mp (Finset.min'_mem S hne)
  have hmax := (mem_resonantMiddleIndices_iff hp.pos hj1).mp (Finset.max'_mem S hne)
  have hN : Odd N := hp.mul (show Odd (2 * q + 1) from ⟨q, rfl⟩)
  have hdN : 2 * p ≤ N := by dsimp [N, resonantParticleCount]; nlinarith
  have hdL : (2 * p) * (q - lo) ≤ N := by
    have hh := Nat.mul_le_mul_left (2 * p) (Nat.sub_le q lo)
    dsimp [N, resonantParticleCount]
    nlinarith
  have hleft : N - (2 * p) * (q - lo) = resonantParticleCount p lo := by
    dsimp only [N]
    rw [resonantParticleCount_sub p (Nat.sub_le q lo)]
    congr 1
    omega
  have hright : N + (2 * p) * (hi - q) = resonantParticleCount p hi := by
    dsimp only [N]
    rw [← resonantParticleCount_add, Nat.add_sub_of_le hhi]
  have hcross' : |actualModelLog B c s (N + 2 * p) j -
      actualModelLog B c s (N - 2 * p) j| ≤ (((2 * p : ℕ) : ℝ)) ^ 2 / 4 * Real.log j := by
    simpa only [N, resonantParticleCount_add, Nat.mul_one,
      ← resonantParticleCount_sub p hq1] using hcross
  have hb := hbound N j (hi - q) (q - lo) hN hdN hdL
    ((le_max_left _ _).trans hjT)
    (by simpa only [hleft] using hmin.1)
    (by simpa only [hright] using middle_window_curvature_upper_gate hj64 hmax.2)
    hcross'
  change (∑ k ∈ Finset.range (hi - q), ‖M (N + (2 * p) * (k + 1))‖) +
    (∑ k ∈ Finset.range (q - lo), ‖M (N - (2 * p) * (k + 1))‖) ≤ _ at hb
  have hset : S = Finset.Icc lo hi := resonantMiddleIndices_eq_Icc hp.pos hj1 hne
  rw [hset, sum_Icc_erase_eq_two_prefixes hlo hhi]
  convert hb using 1
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    rw [resonantParticleCount_add]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkr := Finset.mem_range.mp hk
    have hkq : k + 1 ≤ q := by omega
    dsimp only [N]
    rw [resonantParticleCount_sub p hkq]

end
end IsingBulk.AnisoF002.NegativeHT

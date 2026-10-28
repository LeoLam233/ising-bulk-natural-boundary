import IsingBulk.HT22.Near.ClippedGeometric
import IsingBulk.Preferred22.ShellCover

namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

def dyadicScale (μ ε : ℝ) (n : ℕ) : ℝ :=
  shellCoordinateScale μ (preferredDyadicRadius n) ε

theorem dyadicScale_decay (μ : ℝ) {ε : ℝ} (hε : 0≤ε) (n : ℕ) :
    dyadicScale μ ε (n+1)≤(3/4:ℝ)*dyadicScale μ ε n := by
  unfold dyadicScale
  have he : preferredDyadicRadius (n+1)=preferredDyadicRadius n/2 := by
    unfold preferredDyadicRadius
    rw [pow_succ]
    ring
  rw [he]
  exact shellCoordinateScale_half_three_quarters μ (preferredDyadicRadius_pos n) hε

theorem dyadic_power_decay (μ : ℝ) {ε : ℝ} (hε : 0≤ε) {m : ℕ} (hm : 1≤m) (n : ℕ) :
    dyadicScale μ ε (n+1)^m≤(3/4:ℝ)*dyadicScale μ ε n^m := by
  have hn (n) : 0≤dyadicScale μ ε n :=
    (shellCoordinateScale_pos μ (preferredDyadicRadius_pos n) hε).le
  have hp := pow_le_pow_left₀ (hn (n+1)) (dyadicScale_decay μ hε n) m
  have hq : (3/4:ℝ)^m≤3/4 := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)≤1) hm
  rw [mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right hq (pow_nonneg (hn n) m))

theorem dyadic_near_power_sum (μ : ℝ) {ε δ : ℝ} (hε : 0≤ε) (hδ : 0≤δ)
    {m : ℕ} (hm : 1≤m) :
    Summable (fun n => if dyadicScale μ ε n≤δ then dyadicScale μ ε n^m else 0) ∧
      (∑' n,if dyadicScale μ ε n≤δ then dyadicScale μ ε n^m else 0)≤4*δ^m := by
  classical
  let f := fun n => dyadicScale μ ε n^m
  have hf (n) : 0≤f n := pow_nonneg
    (shellCoordinateScale_pos μ (preferredDyadicRadius_pos n) hε).le m
  have hstep (n) := dyadic_power_decay μ hε hm n
  have hclip := quarter_decay_clipped_sum hf hstep (pow_nonneg hδ m)
  let g := fun n => if dyadicScale μ ε n≤δ then dyadicScale μ ε n^m else 0
  have hg (n) : 0≤g n := by dsimp [g];split <;> first | exact hf n | exact le_refl 0
  have hb (n) : g n ≤ (if f n≤δ^m then f n else 0) := by
    by_cases hn : dyadicScale μ ε n≤δ
    · have hp : f n≤δ^m := pow_le_pow_left₀
        (shellCoordinateScale_pos μ (preferredDyadicRadius_pos n) hε).le hn m
      simp [g,hn,hp,f]
    · by_cases hp : f n≤δ^m
      · simpa [g,hn,hp] using hf n
      · simp [g,hn,hp]
  have hs := hclip.1.of_nonneg_of_le hg hb
  exact ⟨hs,(hs.tsum_le_tsum hb hclip.1).trans hclip.2⟩

end
end IsingBulk.HT22.Near

import IsingBulk.HT22.Near.DyadicScale

namespace IsingBulk.HT22.Near
noncomputable section
open scoped BigOperators

theorem quarter_decay_iterate {f : ℕ → ℝ}
    (hstep : ∀ n, f (n+1)≤(3/4:ℝ)*f n) (k m : ℕ) :
    f (m+k)≤(3/4:ℝ)^m*f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hh := (hstep (m+k)).trans (mul_le_mul_of_nonneg_left ih (by norm_num))
    convert hh using 1
    · congr 1;omega
    · rw [pow_succ];ring

theorem quarter_decay_summable {f : ℕ → ℝ} (hf : ∀ n,0≤f n)
    (hstep : ∀ n,f (n+1)≤(3/4:ℝ)*f n) : Summable f := by
  have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤3/4)
    (by norm_num : (3/4:ℝ)<1)).mul_right (f 0)
  exact hg.of_nonneg_of_le hf (fun n => by simpa using quarter_decay_iterate hstep 0 n)

/-- Uniform near-shell sum starting at its first threshold crossing.
Only a fixed threshold is used; the estimate does not differentiate the cut. -/
theorem quarter_decay_clipped_sum {f : ℕ → ℝ} (hf : ∀ n,0≤f n)
    (hstep : ∀ n,f (n+1)≤(3/4:ℝ)*f n) {B : ℝ} (hB : 0≤B) :
    Summable (fun n => if f n≤B then f n else 0) ∧
      (∑' n,if f n≤B then f n else 0)≤4*B := by
  classical
  let g := fun n => if f n≤B then f n else 0
  have hg0 (n) : 0≤g n := by dsimp [g];split <;> first | exact hf n | exact le_refl 0
  have hgf (n) : g n≤f n := by dsimp [g];split <;> simp_all
  have hs := quarter_decay_summable hf hstep
  have hg := hs.of_nonneg_of_le hg0 hgf
  refine ⟨hg,?_⟩
  change (∑' n,g n)≤4*B
  by_cases hex : ∃ n,f n≤B
  · let k := Nat.find hex
    have hk : f k≤B := Nat.find_spec hex
    have hzero : ∑ n∈Finset.range k,g n=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hn' : n<Nat.find hex := Finset.mem_range.mp hn
      have hnot := Nat.find_min hex hn'
      simp [g,hnot]
    have hsum := hg.sum_add_tsum_nat_add k
    rw [hzero,zero_add] at hsum
    rw [←hsum]
    have hi : Function.Injective (fun n : ℕ => n+k) := by
      intro a b h
      change a+k=b+k at h
      omega
    have hsuff := hg.comp_injective hi
    have hgeom := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤3/4)
      (by norm_num : (3/4:ℝ)<1)).mul_right (f k)
    calc
      _ ≤ ∑' n,(3/4:ℝ)^n*f k := hsuff.tsum_le_tsum
        (fun n => (hgf (n+k)).trans (quarter_decay_iterate hstep k n)) hgeom
      _ = 4*f k := by rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)];norm_num
      _ ≤ 4*B := mul_le_mul_of_nonneg_left hk (by norm_num)
  · have hz : g=0 := by
      funext n
      have hn : ¬ f n≤B := fun h => hex ⟨n,h⟩
      simp [g,hn]
    simp only [hz,Pi.zero_apply,tsum_zero]
    positivity

end
end IsingBulk.HT22.Near

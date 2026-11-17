import IsingBulk.AnisoF002.C03.NegativeHighParticleThreshold
import IsingBulk.AnisoF002.C03.NegativeTailDominanceScales

/-!
# The full infinite high-particle sum

The cutoff is exactly N² > j / sqrt(log j).  The bound sums every
population above that cutoff and is stable under any injective particle
progression, in particular the complete rational-resonance progression.
The constant is fixed before the Taylor order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators Classical

def filteredHighParticleEnvelope (C : ℝ) (j N : ℕ) : ℝ :=
  if highParticleThreshold j < (N : ℝ) ^ 2 then
    Real.exp (highParticleExponent j C ((N : ℝ) ^ 2)) else 0

theorem filteredHighParticleEnvelope_nonneg (C : ℝ) (j N : ℕ) :
    0 ≤ filteredHighParticleEnvelope C j N := by
  unfold filteredHighParticleEnvelope
  split_ifs <;> positivity

theorem complete_filtered_high_envelope {C : ℝ} {j : ℕ}
    (hj : 0 < j) (ht : 256 ≤ Real.log (j : ℝ))
    (hC : 16 * (C + 1) ≤ Real.log (j : ℝ)) :
    Summable (filteredHighParticleEnvelope C j) ∧
      (∑' N : ℕ, filteredHighParticleEnvelope C j N) ≤
        Real.exp ((j : ℝ) * Real.log j - (j : ℝ) / 2 * Real.log (Real.log j) -
          (j : ℝ) / 8 * Real.sqrt (Real.log j)) * ∑' m : ℕ, Real.exp (-(m : ℝ)) := by
  let X := highParticleThreshold j
  let K : ℕ := ⌈Real.sqrt X⌉₊
  have hX : 0 < X := highParticleThreshold_pos hj (by linarith)
  have hroot : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hceil : Real.sqrt X ≤ (K : ℝ) := Nat.le_ceil _
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := hroot.trans_le hceil
    exact_mod_cast this
  have hKsq : X ≤ (K : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hX.le]
  obtain ⟨hs, hb⟩ := complete_high_particle_window_tail hj ht hC hKpos hKsq
  have hbound (m : ℕ) : filteredHighParticleEnvelope C j (m + K) ≤
      Real.exp (highParticleExponent j C (((K + m : ℕ) : ℝ) ^ 2)) := by
    unfold filteredHighParticleEnvelope
    split_ifs
    · simp only [Nat.add_comm, le_refl]
    · positivity
  have htail : Summable (fun m : ℕ => filteredHighParticleEnvelope C j (m + K)) :=
    hs.of_nonneg_of_le (fun m => filteredHighParticleEnvelope_nonneg C j (m + K)) hbound
  have hfull : Summable (filteredHighParticleEnvelope C j) := (summable_nat_add_iff K).mp htail
  have hzero : ∑ N ∈ Finset.range K, filteredHighParticleEnvelope C j N = 0 := by
    apply Finset.sum_eq_zero
    intro N hN
    have hNr : (N : ℝ) < Real.sqrt X := Nat.lt_ceil.mp (Finset.mem_range.mp hN)
    have hNsq : ¬ X < (N : ℝ) ^ 2 := by
      nlinarith [Real.sq_sqrt hX.le, Nat.cast_nonneg (α := ℝ) N]
    exact ite_eq_right hNsq
  have hsum := hfull.sum_add_tsum_nat_add K
  rw [hzero, zero_add] at hsum
  refine ⟨hfull, ?_⟩
  rw [← hsum]
  exact (htail.tsum_le_tsum hbound hs).trans hb

theorem exists_complete_high_subsequence_bound {C : ℝ} (hC0 : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ, 0 < j → 256 ≤ Real.log (j : ℝ) →
      16 * (C + 1) ≤ Real.log (j : ℝ) →
      ∀ e : ℕ → ℕ, Function.Injective e → ∀ f : ℕ → ℝ,
      (∀ q, 0 ≤ f q) →
      (∀ q, highParticleThreshold j < (e q : ℝ) ^ 2 →
        f q ≤ Real.exp (2 * (j : ℝ) * Real.log (e q : ℝ) -
          (e q : ℝ) ^ 2 / 2 * Real.log (e q : ℝ) + C * (e q : ℝ) ^ 2 + C * j + C)) →
      Summable (fun q : ℕ => if highParticleThreshold j < (e q : ℝ) ^ 2 then f q else 0) ∧
      (∑' q : ℕ, if highParticleThreshold j < (e q : ℝ) ^ 2 then f q else 0) ≤
        Real.exp (completeHighExponent A j) := by
  let G : ℝ := ∑' m : ℕ, Real.exp (-(m : ℝ))
  let A : ℝ := C + G + 1
  have hG : 0 ≤ G := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hA : 0 < A := by dsimp [A]; linarith
  refine ⟨A, hA, ?_⟩
  intro j hj ht hC e he f hf hbound
  obtain ⟨hs, hb⟩ := complete_filtered_high_envelope hj ht hC
  let F : ℕ → ℝ := fun N => Real.exp (C * j + C) * filteredHighParticleEnvelope C j N
  let g : ℕ → ℝ := fun q => if highParticleThreshold j < (e q : ℝ) ^ 2 then f q else 0
  have hFs : Summable F := hs.mul_left _
  have hF0 (N : ℕ) : 0 ≤ F N := mul_nonneg (Real.exp_pos _).le
    (filteredHighParticleEnvelope_nonneg C j N)
  have hg0 (q : ℕ) : 0 ≤ g q := by
    dsimp [g]
    split_ifs
    · exact hf q
    · exact le_rfl
  have hle (q : ℕ) : g q ≤ F (e q) := by
    dsimp [g, F, filteredHighParticleEnvelope]
    split_ifs with hq
    · apply (hbound q hq).trans_eq
      rw [← Real.exp_add, highParticleExponent_square_form]
      congr 1
      ring
    · simp only [mul_zero, le_refl]
  have hgs : Summable g := (hFs.comp_injective he).of_nonneg_of_le hg0 hle
  refine ⟨hgs, ?_⟩
  have hsum : (∑' q : ℕ, g q) ≤ ∑' N : ℕ, F N :=
    hgs.tsum_le_tsum_of_inj e he (fun N _ => hF0 N) hle hFs
  apply hsum.trans
  calc
    _ = Real.exp (C * j + C) * ∑' N : ℕ, filteredHighParticleEnvelope C j N := tsum_mul_left
    _ ≤ Real.exp (C * j + C) *
        (Real.exp ((j : ℝ) * Real.log j - (j : ℝ) / 2 * Real.log (Real.log j) -
          (j : ℝ) / 8 * Real.sqrt (Real.log j)) * G) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ Real.exp (C * j + C) *
        (Real.exp ((j : ℝ) * Real.log j - (j : ℝ) / 2 * Real.log (Real.log j) -
          (j : ℝ) / 8 * Real.sqrt (Real.log j)) * Real.exp G) := by
      gcongr
      linarith [Real.add_one_le_exp G]
    _ ≤ _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [completeHighExponent, A]
      nlinarith [Nat.cast_nonneg (α := ℝ) j]

end
end IsingBulk.AnisoF002.NegativeHT

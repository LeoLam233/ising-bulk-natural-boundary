import IsingBulk.AnisoF002.C03.NegativeActualCompetitorNorms
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The complete resonant middle-particle window

The finite set below is exactly all resonant odd particle counts between
the physical low and high cutoffs.  It is a consecutive interval in the
resonant index.  Its deletion of a selected center is exactly the two
complete competitor prefixes, with no omitted particle class.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem sum_Icc_erase_eq_two_prefixes {lo q hi : ℕ} (hlo : lo ≤ q) (hhi : q ≤ hi)
    (f : ℕ → ℝ) :
    (∑ a ∈ (Finset.Icc lo hi).erase q, f a) =
      (∑ k ∈ Finset.range (hi - q), f (q + (k + 1))) +
      (∑ k ∈ Finset.range (q - lo), f (q - (k + 1))) := by
  have hset : (Finset.Icc lo hi).erase q = Finset.Ico lo q ∪ Finset.Ioc q hi := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Ico lo q) (Finset.Ioc q hi) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha' := Finset.mem_Ico.mp ha
    have hb' := Finset.mem_Ioc.mp hb
    omega
  have hleft : (∑ a ∈ Finset.Ico lo q, f a) =
      ∑ k ∈ Finset.range (q - lo), f (q - (k + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    calc
      _ = ∑ k ∈ Finset.range (q - lo), f (lo + (q - lo - 1 - k)) :=
        (Finset.sum_range_reflect (fun k => f (lo + k)) (q - lo)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkr := Finset.mem_range.mp hk
        congr 1
        omega
  have hright : (∑ a ∈ Finset.Ioc q hi, f a) =
      ∑ k ∈ Finset.range (hi - q), f (q + (k + 1)) := by
    have hs : Finset.Ioc q hi = Finset.Ico (q + 1) (hi + 1) := by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hs, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    omega
  rw [hset, Finset.sum_union hdisj, hleft, hright, add_comm]

def resonantParticleCount (p k : ℕ) : ℕ := p * (2 * k + 1)

theorem resonantParticleCount_mono (p : ℕ) : Monotone (resonantParticleCount p) := by
  intro a b hab
  exact Nat.mul_le_mul_left p (by omega)

theorem resonantParticleCount_pos {p : ℕ} (hp : 0 < p) (k : ℕ) :
    0 < resonantParticleCount p k := by unfold resonantParticleCount; positivity

theorem index_le_resonantParticleCount {p : ℕ} (hp : 0 < p) (k : ℕ) :
    k ≤ resonantParticleCount p k := by
  have hh := Nat.mul_le_mul_right (2 * k + 1) hp
  unfold resonantParticleCount
  nlinarith

def resonantMiddleIndices (p j : ℕ) : Finset ℕ :=
  (Finset.range (j + 1)).filter fun k =>
    Real.log j ≤ (resonantParticleCount p k : ℝ) ∧
      (resonantParticleCount p k : ℝ) ^ 2 ≤ highParticleThreshold j

theorem mem_resonantMiddleIndices_iff {p j k : ℕ} (hp : 0 < p)
    (hj : 1 ≤ Real.log j) :
    k ∈ resonantMiddleIndices p j ↔
      Real.log j ≤ (resonantParticleCount p k : ℝ) ∧
        (resonantParticleCount p k : ℝ) ^ 2 ≤ highParticleThreshold j := by
  simp only [resonantMiddleIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hs : 1 ≤ Real.sqrt (Real.log j) := by
      have hh := Real.sq_sqrt (show 0 ≤ Real.log j by linarith)
      have hnonneg := Real.sqrt_nonneg (Real.log j)
      nlinarith
    have hthreshold : highParticleThreshold j ≤ (j : ℝ) :=
      div_le_self (Nat.cast_nonneg j) hs
    have hcount1 : (1 : ℝ) ≤ resonantParticleCount p k := by
      exact_mod_cast resonantParticleCount_pos hp k
    have hcount : (resonantParticleCount p k : ℝ) ≤ (j : ℝ) := by
      have hh := h.2.trans hthreshold
      nlinarith
    have hcountNat : resonantParticleCount p k ≤ j := by exact_mod_cast hcount
    have hk := (index_le_resonantParticleCount hp k).trans hcountNat
    omega

theorem resonantMiddleIndices_eq_Icc {p j : ℕ} (hp : 0 < p)
    (hj : 1 ≤ Real.log j) (hne : (resonantMiddleIndices p j).Nonempty) :
    resonantMiddleIndices p j = Finset.Icc
      ((resonantMiddleIndices p j).min' hne) ((resonantMiddleIndices p j).max' hne) := by
  let S := resonantMiddleIndices p j
  have hmin := Finset.min'_mem S hne
  have hmax := Finset.max'_mem S hne
  have hminData := (mem_resonantMiddleIndices_iff hp hj).mp hmin
  have hmaxData := (mem_resonantMiddleIndices_iff hp hj).mp hmax
  ext k
  constructor
  · intro hk
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
  · intro hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
    apply (mem_resonantMiddleIndices_iff hp hj).mpr
    have hlowCount : (resonantParticleCount p (S.min' hne) : ℝ) ≤
        (resonantParticleCount p k : ℝ) := by
      exact_mod_cast resonantParticleCount_mono p hlo
    have hhighCount : (resonantParticleCount p k : ℝ) ≤
        (resonantParticleCount p (S.max' hne) : ℝ) := by
      exact_mod_cast resonantParticleCount_mono p hhi
    refine ⟨hminData.1.trans hlowCount, ?_⟩
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hhighCount 2).trans hmaxData.2

end
end IsingBulk.AnisoF002.NegativeHT

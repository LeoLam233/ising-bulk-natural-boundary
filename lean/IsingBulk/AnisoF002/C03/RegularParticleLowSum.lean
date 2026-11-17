import IsingBulk.AnisoF002.C03.NegativeResonantReindex
import IsingBulk.AnisoF002.C03.NegativeTailDominanceScales

/-!
# Every low-particle physical residue

The complete coefficient identity bounds the literal residue by the
physical Taylor coefficient and its actual analytic remainder.  The
strict low cutoff is disjoint from the closed middle window.  Reindexing
retains every resonant population and uses the original odd-particle
coefficient, including all finite exceptional populations.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped Topology BigOperators Classical

def resonantLowIndices (p j : ℕ) : Finset ℕ :=
  (Finset.range (j + 1)).filter fun q =>
    (resonantParticleCount p q : ℝ) < Real.log (j : ℝ)

theorem mem_resonantLowIndices_iff {p j q : ℕ} (hp : 0 < p) (hj : 0 < j) :
    q ∈ resonantLowIndices p j ↔
      (resonantParticleCount p q : ℝ) < Real.log (j : ℝ) := by
  simp only [resonantLowIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro hq
    refine ⟨?_, hq⟩
    have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hj : (0 : ℝ) < j)
    have hqN : (q : ℝ) ≤ resonantParticleCount p q := by
      exact_mod_cast index_le_resonantParticleCount hp q
    have hqj : (q : ℝ) < j := by linarith
    have : q < j := by exact_mod_cast hqj
    omega

theorem resonantLowIndices_image_subset {p j : ℕ} (hp : Odd p) (hj : 0 < j) :
    (resonantLowIndices p j).image (resonantOddIndex p) ⊆ lowOddParticleIndices j := by
  intro n hn
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
  apply (mem_lowOddParticleIndices hj).mpr
  rw [resonantOddIndex_particle hp]
  exact ((mem_resonantLowIndices_iff hp.pos hj).mp hq).le

theorem completeCyclePoleCoefficient_resonant_eq {b B : ℂ → ℂ}
    {φ radius cutoff M kappa : ℝ} {a p : ℕ} (hp : Odd p) (hcop : a.Coprime p)
    (hφ : φ = 2 * Real.pi * a / p)
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) radius cutoff M kappa)
    (j q : ℕ) :
    completeCyclePoleCoefficient D j (resonantOddIndex p q) =
      innerCyclePoleCoefficient (D (resonantOddIndex p q)) j := by
  have hres : Complex.exp (-(((2 * resonantOddIndex p q + 1 : ℕ) : ℂ) *
      ((φ : ℂ) * Complex.I))) = 1 := by
    rw [hφ]
    apply (rational_negative_phase_resonance_iff hp.pos.ne' hcop _).mpr
    exact (exists_resonantOddIndex_iff hp).mp ⟨q, rfl⟩
  simp only [completeCyclePoleCoefficient, hres, ↓reduceIte]

theorem complete_low_residue_sum_of_identity {b B : ℂ → ℂ}
    {φ radius cutoff Mi ki A : ℝ}
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) radius cutoff Mi ki)
    (hs : 0 ≤ cutoff)
    (hcoeff : ∀ j n : ℕ, physicalOddTaylorCoefficient b B φ j n =
      completeCyclePoleCoefficient D j n +
        iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ))
    (hrem : ∀ j : ℕ,
      Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)‖) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)‖) ≤ Real.exp (completeAnalyticExponent A j))
    (j : ℕ) :
    (∑ n ∈ lowOddParticleIndices j, ‖completeCyclePoleCoefficient D j n‖) ≤
      (∑ n ∈ lowOddParticleIndices j, ‖physicalOddTaylorCoefficient b B φ j n‖) +
        Real.exp (completeAnalyticExponent A j) := by
  have hpoint (n : ℕ) : ‖completeCyclePoleCoefficient D j n‖ ≤
      ‖physicalOddTaylorCoefficient b B φ j n‖ +
        ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ)‖ := by
    have he : completeCyclePoleCoefficient D j n = physicalOddTaylorCoefficient b B φ j n -
        iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ) := by
      rw [hcoeff j n]
      ring
    rw [he]
    exact norm_sub_le _ _
  calc
    _ ≤ ∑ n ∈ lowOddParticleIndices j,
        (‖physicalOddTaylorCoefficient b B φ j n‖ +
          ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ)‖) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = _ := by rw [Finset.sum_add_distrib]
    _ ≤ _ := by
      gcongr
      exact ((hrem j).1.sum_le_tsum (lowOddParticleIndices j)
        (fun _ _ => norm_nonneg _)).trans (hrem j).2

theorem exists_complete_low_residue_bound {b B : ℂ → ℂ}
    {φ radius cutoff Mi ki Ar : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) radius cutoff Mi ki)
    (hs : 0 ≤ cutoff)
    (hcoeff : ∀ j n : ℕ, physicalOddTaylorCoefficient b B φ j n =
      completeCyclePoleCoefficient D j n +
        iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ))
    (hrem : ∀ j : ℕ,
      Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)‖) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)‖) ≤ Real.exp (completeAnalyticExponent Ar j)) :
    ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ, 0 < j →
      (∑ n ∈ lowOddParticleIndices j, ‖completeCyclePoleCoefficient D j n‖) ≤
        Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j) := by
  obtain ⟨Al, hAl, hlow⟩ := exists_actual_complete_low_particle_bound hb hB hφ hπ hBi hbsq
  let A := max Al Ar
  have hA : 0 < A := hAl.trans_le (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro j hj
  have hl := (complete_low_residue_sum_of_identity D hs hcoeff hrem j).trans
    (add_le_add (hlow j hj) (le_refl (Real.exp (completeAnalyticExponent Ar j))))
  apply hl.trans
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    dsimp [completeLowExponent]
    have hmul := mul_le_mul_of_nonneg_right (show Al ≤ A from le_max_left _ _)
      (Nat.cast_nonneg (α := ℝ) j)
    linarith [show Al ≤ A from le_max_left _ _]
  · apply Real.exp_le_exp.mpr
    dsimp [completeAnalyticExponent]
    have hmul := mul_le_mul_of_nonneg_right (show Ar ≤ A from le_max_right _ _)
      (Nat.cast_nonneg (α := ℝ) j)
    linarith [show Ar ≤ A from le_max_right _ _]

theorem resonant_low_residue_sum_le_complete {b B : ℂ → ℂ}
    {φ radius cutoff Mi ki : ℝ} {a p : ℕ}
    (hp : Odd p) (hcop : a.Coprime p) (hφ : φ = 2 * Real.pi * a / p)
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) radius cutoff Mi ki)
    {j : ℕ} (hj : 0 < j) :
    (∑ q ∈ resonantLowIndices p j,
      ‖innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖) ≤
      ∑ n ∈ lowOddParticleIndices j, ‖completeCyclePoleCoefficient D j n‖ := by
  calc
    _ = ∑ q ∈ resonantLowIndices p j,
        ‖completeCyclePoleCoefficient D j (resonantOddIndex p q)‖ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [completeCyclePoleCoefficient_resonant_eq hp hcop hφ]
    _ = ∑ n ∈ (resonantLowIndices p j).image (resonantOddIndex p),
        ‖completeCyclePoleCoefficient D j n‖ := by
      rw [Finset.sum_image]
      intro q _ k _ hqk
      exact resonantOddIndex_injective hp.pos hqk
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (resonantLowIndices_image_subset hp hj) (fun _ _ _ => norm_nonneg _)

end
end IsingBulk.AnisoF002.NegativeHT

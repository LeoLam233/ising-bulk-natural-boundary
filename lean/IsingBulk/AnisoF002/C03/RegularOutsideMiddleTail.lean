import IsingBulk.AnisoF002.C03.RegularParticleLowSum
import IsingBulk.AnisoF002.C03.RegularPhysicalHighTail

/-!
# The complete actual residue sum outside the exact middle window

The finite middle set is the unchanged resonantMiddleIndices.  Every
remaining resonant particle is controlled by the strict low range or
the full infinite high range.  The original odd-particle reindexing is
injective and every nonresonant residue is exactly zero.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators Classical

theorem resonant_high_residue_sum_le_complete {b B : ℂ → ℂ}
    {φ radius cutoff Mi ki : ℝ} {a p : ℕ}
    (hp : Odd p) (hcop : a.Coprime p) (hφ : φ = 2 * Real.pi * a / p)
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) radius cutoff Mi ki)
    (j : ℕ)
    (hs : Summable (fun n : ℕ => if highParticleThreshold j < ((2 * n + 1 : ℕ) : ℝ) ^ 2
      then ‖completeCyclePoleCoefficient D j n‖ else 0)) :
    Summable (fun q : ℕ => if highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2
      then ‖innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖ else 0) ∧
    (∑' q : ℕ, if highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2
      then ‖innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖ else 0) ≤
    ∑' n : ℕ, if highParticleThreshold j < ((2 * n + 1 : ℕ) : ℝ) ^ 2
      then ‖completeCyclePoleCoefficient D j n‖ else 0 := by
  let F : ℕ → ℝ := fun n => if highParticleThreshold j < ((2 * n + 1 : ℕ) : ℝ) ^ 2
    then ‖completeCyclePoleCoefficient D j n‖ else 0
  let G : ℕ → ℝ := fun q => if highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2
    then ‖innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖ else 0
  have he (q : ℕ) : G q = F (resonantOddIndex p q) := by
    dsimp [F, G]
    rw [resonantOddIndex_particle hp, completeCyclePoleCoefficient_resonant_eq hp hcop hφ]
  have hGs : Summable G := (hs.comp_injective (resonantOddIndex_injective hp.pos)).congr
    (fun q => (he q).symm)
  refine ⟨hGs, ?_⟩
  exact hGs.tsum_le_tsum_of_inj (resonantOddIndex p) (resonantOddIndex_injective hp.pos)
    (fun n _ => by split_ifs <;> positivity)
    (fun q => (he q).le) hs

theorem complete_outside_middle_sum_bound {p j : ℕ} (hp : 0 < p)
    (hjlog : 1 ≤ Real.log (j : ℝ)) (f : ℕ → ℂ) {A : ℝ}
    (hlow : (∑ q ∈ resonantLowIndices p j, ‖f q‖) ≤
      Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j))
    (hhigh : Summable (fun q : ℕ => if highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2
      then ‖f q‖ else 0))
    (hhighBound : (∑' q : ℕ, if highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2
      then ‖f q‖ else 0) ≤ Real.exp (completeHighExponent A j)) :
    Summable (fun q : ℕ => ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ) else f q‖) ∧
    (∑' q : ℕ, ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ) else f q‖) ≤
      Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j) +
        Real.exp (completeHighExponent A j) := by
  have hj : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    norm_num [hz] at hjlog
  let L : ℕ → ℝ := fun q => if q ∈ resonantLowIndices p j then ‖f q‖ else 0
  let H : ℕ → ℝ := fun q => if highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2
    then ‖f q‖ else 0
  let O : ℕ → ℝ := fun q => ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ) else f q‖
  have hLs : Summable L := summable_of_ne_finset_zero (s := resonantLowIndices p j)
    (fun q hq => by simp only [L, hq, ↓reduceIte])
  have hLsum : (∑' q : ℕ, L q) = ∑ q ∈ resonantLowIndices p j, ‖f q‖ := by
    calc
      _ = ∑ q ∈ resonantLowIndices p j, L q :=
        tsum_eq_sum (fun q hq => by simp only [L, hq, ↓reduceIte])
      _ = _ := Finset.sum_congr rfl (fun q hq => by simp only [L, hq, ↓reduceIte])
  have hL0 (q : ℕ) : 0 ≤ L q := by dsimp [L]; split_ifs <;> positivity
  have hH0 (q : ℕ) : 0 ≤ H q := by dsimp [H]; split_ifs <;> positivity
  have hpoint (q : ℕ) : O q ≤ L q + H q := by
    by_cases hmid : q ∈ resonantMiddleIndices p j
    · simpa only [O, hmid, ↓reduceIte, norm_zero] using add_nonneg (hL0 q) (hH0 q)
    · have hmid' := (mem_resonantMiddleIndices_iff hp hjlog).not.mp hmid
      by_cases hl : (resonantParticleCount p q : ℝ) < Real.log (j : ℝ)
      · have hlmem := (mem_resonantLowIndices_iff hp hj).mpr hl
        have hq : L q = ‖f q‖ := by simp only [L, hlmem, ↓reduceIte]
        dsimp [O]
        rw [ite_eq_right hmid, hq]
        linarith [hH0 q]
      · have hh : highParticleThreshold j < (resonantParticleCount p q : ℝ) ^ 2 := by
          by_contra hn
          exact hmid' ⟨le_of_not_gt hl, le_of_not_gt hn⟩
        have hq : H q = ‖f q‖ := by simp only [H, hh, ↓reduceIte]
        dsimp [O]
        rw [ite_eq_right hmid, hq]
        linarith [hL0 q]
  have hOs : Summable O := (hLs.add hhigh).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨hOs, ?_⟩
  calc
    _ ≤ ∑' q : ℕ, (L q + H q) := hOs.tsum_le_tsum hpoint (hLs.add hhigh)
    _ = (∑' q : ℕ, L q) + ∑' q : ℕ, H q := hLs.tsum_add hhigh
    _ ≤ _ := by rw [hLsum]; exact add_le_add hlow hhighBound

theorem completeLowExponent_mono {A B : ℝ} (hAB : A ≤ B) (j : ℕ) :
    completeLowExponent A j ≤ completeLowExponent B j := by
  unfold completeLowExponent
  nlinarith [mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg (α := ℝ) j)]

theorem completeAnalyticExponent_mono {A B : ℝ} (hAB : A ≤ B) (j : ℕ) :
    completeAnalyticExponent A j ≤ completeAnalyticExponent B j := by
  unfold completeAnalyticExponent
  nlinarith [mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg (α := ℝ) j)]

theorem completeHighExponent_mono {A B : ℝ} (hAB : A ≤ B) (j : ℕ) :
    completeHighExponent A j ≤ completeHighExponent B j := by
  unfold completeHighExponent
  nlinarith [mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg (α := ℝ) j)]

theorem exists_actual_outside_middle_residue_bound {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ r s Mi ki Ar : ℝ, 0 < r → 0 < s → 0 ≤ Mi → s ≤ s0 →
      ∀ D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki,
      ∀ hs : 0 ≤ s,
      (∀ j n : ℕ, physicalOddTaylorCoefficient b B φ j n = completeCyclePoleCoefficient D j n +
        iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ)) →
      (∀ j : ℕ,
        Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
          (j.factorial : ℂ)‖) ∧
        (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
          (j.factorial : ℂ)‖) ≤ Real.exp (completeAnalyticExponent Ar j)) →
      ∃ A : ℝ, 0 < A ∧ ∀ a p : ℕ, Odd p → a.Coprime p → φ = 2 * Real.pi * a / p →
      ∀ᶠ j : ℕ in atTop,
        Summable (fun q : ℕ => ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ)
          else innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖) ∧
        (∑' q : ℕ, ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ)
          else innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖) ≤
          Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j) +
            Real.exp (completeHighExponent A j) := by
  obtain ⟨s0, Ah, hs0, hAh, hhigh⟩ := exists_actual_complete_high_particle_bound hb hB hφ hπ hBi hbsq
  refine ⟨s0, hs0, ?_⟩
  intro r s Mi ki Ar hr hs hMi hss0 D hs' hcoeff hrem
  obtain ⟨Al, hAl, hlow⟩ := exists_complete_low_residue_bound hb hB hφ hπ hBi hbsq D hs' hcoeff hrem
  let A := max Al Ah
  refine ⟨A, hAl.trans_le (le_max_left _ _), ?_⟩
  intro a p hp hcop hrat
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hhigh r s Mi ki hr hs hMi hss0 D,
    hlog.eventually (eventually_ge_atTop 1)] with j hjhigh hjlog
  have hj : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    norm_num [hz] at hjlog
  obtain ⟨hHs, hHb⟩ := resonant_high_residue_sum_le_complete hp hcop hrat D j hjhigh.1
  apply complete_outside_middle_sum_bound hp.pos hjlog
    (fun q => innerCyclePoleCoefficient (D (resonantOddIndex p q)) j)
  · apply ((resonant_low_residue_sum_le_complete hp hcop hrat D hj).trans (hlow j hj)).trans
    exact add_le_add
      (Real.exp_le_exp.mpr (completeLowExponent_mono (le_max_left Al Ah) j))
      (Real.exp_le_exp.mpr (completeAnalyticExponent_mono (le_max_left Al Ah) j))
  · exact hHs
  · exact (hHb.trans hjhigh.2).trans
      (Real.exp_le_exp.mpr (completeHighExponent_mono (le_max_right Al Ah) j))

end
end IsingBulk.AnisoF002.NegativeHT

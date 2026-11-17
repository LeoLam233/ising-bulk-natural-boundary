import IsingBulk.AnisoF002.C03.RegularWindingSectorPartition
import IsingBulk.AnisoF002.C03.RegularWindingSectorCenter

/-!
# Integrability of every literal winding sector

The measurable sharp cutoff and the bound on the original complete torus
are transported to each genuine sector.  No extra sectorwise integrability
premise is needed in the resulting all-winding measure identity.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators Classical

theorem windingAngles_continuous (n : ℕ) (w : ℤ) : Continuous (windingAngles n w) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [windingAngles_last]
    fun_prop
  · simpa only [windingAngles_castSucc] using continuous_apply j

theorem windingSquare_continuous (n : ℕ) (w : ℤ) : Continuous (windingSquare n w) :=
  continuous_finsetSum _ (fun i _ => ((continuous_apply i).comp (windingAngles_continuous n w)).pow 2)

theorem windingSquare_eq_shortSquare_of_cut {n : ℕ} {w : ℤ} {s : ℝ} {x : Fin n → ℝ}
    (hs : s < Real.pi ^ 2) (hx : windingSquare n w x ≤ s) :
    windingSquare n w x = angularShortSquare (windingAngles n w x) := by
  apply Finset.sum_congr rfl
  intro i _
  exact (unsignedShortAngle_sq_of_abs_le (windingSquare_coordinate_bound hs hx i).le).symm

theorem windingCutDensity_measurable {n : ℕ} {s : ℝ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hs : s < Real.pi ^ 2) (hF : Measurable (shortCutDensity s F)) (w : ℤ) :
    Measurable (windingCutDensity n s F w) := by
  have he : windingCutDensity n s F w = fun x =>
      if windingSquare n w x ≤ s then shortCutDensity s F (windingAngles n w x) else 0 := by
    funext x
    by_cases hx : windingSquare n w x ≤ s
    · have hq : angularShortSquare (windingAngles n w x) ≤ s := by
        rwa [← windingSquare_eq_shortSquare_of_cut hs hx]
      simp only [windingCutDensity, shortCutDensity, hx, hq, ↓reduceIte]
    · simp only [windingCutDensity, hx, ↓reduceIte]
  rw [he]
  exact Measurable.ite
    (measurableSet_le (windingSquare_continuous n w).measurable measurable_const)
    (hF.comp (windingAngles_continuous n w).measurable) measurable_const

theorem windingCutDensity_bound {n : ℕ} {s E : ℝ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hp : AllAnglePeriodic (shortCutDensity s F)) (hn : Odd (n + 1))
    (hs : s < Real.pi ^ 2) (hE : 0 ≤ E)
    (hbound : ∀ q : Fin n → ℝ, ‖shortCutDensity s F (negativeConstrainedAngles q)‖ ≤ E)
    {w : ℤ} (hw : Odd w) (q : Fin n → ℝ) : ‖windingCutDensity n s F w q‖ ≤ E := by
  by_cases hcut : windingSquare n w q ≤ s
  · have he := windingIndex_eq_of_sector hw hs hcut
    have hsq : angularShortSquare (windingAngles n w q) ≤ s := by
      rwa [← windingSquare_eq_shortSquare_of_cut hs hcut]
    calc
      _ = ‖shortCutDensity s F (windingAngles n w q)‖ := by
        simp only [windingCutDensity, shortCutDensity, hcut, hsq, ↓reduceIte]
      _ = ‖shortCutDensity s F (windingAngles n 1 q)‖ := by
        rw [allAnglePeriodic_index_reduce hp q, he]
      _ = ‖shortCutDensity s F (negativeConstrainedAngles (q + fun _ => Real.pi))‖ := by
        rw [allAnglePeriodic_negative_half_shift hp hn]
      _ ≤ E := hbound _
  · simpa only [windingCutDensity, hcut, ↓reduceIte, norm_zero] using hE

theorem windingCutDensity_integrable {n : ℕ} {s E : ℝ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hp : AllAnglePeriodic (shortCutDensity s F)) (hn : Odd (n + 1))
    (hs : s < Real.pi ^ 2) (hF : Measurable (shortCutDensity s F)) (hE : 0 ≤ E)
    (hbound : ∀ q : Fin n → ℝ, ‖shortCutDensity s F (negativeConstrainedAngles q)‖ ≤ E)
    {w : ℤ} (hw : Odd w) : Integrable (windingCutDensity n s F w) := by
  have hm := windingCutDensity_measurable F hs hF w
  have hfin : volume (regularAngularBox n) < ⊤ := (regularAngularBox_compact n).measure_lt_top
  have hi : IntegrableOn (windingCutDensity n s F w) (regularAngularBox n) :=
    IntegrableOn.of_bound hfin hm.aestronglyMeasurable E
      (Filter.Eventually.of_forall (windingCutDensity_bound F hp hn hs hE hbound hw))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro q hq
  by_contra hnq
  exact hq (windingCutDensity_eq_zero_off_box F hs w q hnq)

theorem windingSector_integral_complete {n : ℕ} {s E : ℝ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hp : AllAnglePeriodic (shortCutDensity s F)) (hn : Odd (n + 1))
    (hs : s < Real.pi ^ 2) (hF : Measurable (shortCutDensity s F)) (hE : 0 ≤ E)
    (hbound : ∀ q : Fin n → ℝ, ‖shortCutDensity s F (negativeConstrainedAngles q)‖ ≤ E) :
    (∫ q in regularAngularBox n, shortCutDensity s F (negativeConstrainedAngles q)) =
      ∑ w ∈ windingSectorIndices n, ∫ v : Angular.constrainedPlane n,
        if ‖v‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) ≤ s then
          F (centeredWindingAngles w v) else 0 ∂Angular.independentMeasure n := by
  rw [windingSector_integral F hp hn hs
    (fun w hw => windingCutDensity_integrable F hp hn hs hF hE hbound (Finset.mem_filter.mp hw).2)]
  apply Finset.sum_congr rfl
  intro w _
  exact windingSector_integral_center n w s F

end
end IsingBulk.AnisoF002.NegativeHT

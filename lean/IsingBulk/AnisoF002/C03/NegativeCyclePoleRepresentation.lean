import IsingBulk.AnisoF002.C03.NegativeInnerCycleRemainder
import IsingBulk.AnisoF002.C03.NegativeRationalPoleIntegral
import IsingBulk.AnisoF002.C03.NegativePhysicalCycleControl
import IsingBulk.AnisoF002.C03.NegativeCycleMeasurableDensity

/-!
# Measurable representatives of the exact complete real-cycle residue

The representative agrees with the literal residue on every inner angle
and vanishes elsewhere.  Its measurability is proved by evaluating the
already established exact pole subtraction at zero.  This preserves the
actual moving pole, the full numerator, and its physical normalization.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

namespace InnerRemainderFamily
variable {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {N : ℕ}
  (d : InnerRemainderFamily b B φ N r s M kappa)

def actualResidue (q : Fin N → ℝ) : ℂ :=
  2 * completeNegativeNumerator N b (negativeGlobalPhase B φ) 0 (d.pole q)
      (fun i => (q i : ℂ)) / deriv (realPhaseTotal B φ N q) (d.pole q)

theorem realCycleRemainderDensity_eq (hs : 0 ≤ s) {q : Fin N → ℝ}
    (hq : angularShortSquare q ≤ s) (t : ℂ) :
    d.realCycleRemainderDensity hs t q = d.remainder t ⟨q, hq⟩ := by
  simp only [realCycleRemainderDensity, hq, ↓reduceIte, innerAngularRetraction, innerAngularClip]

theorem residue_from_center (hr : 0 < r) (hs : 0 ≤ s) (hN : 0 < N)
    (hres : Complex.exp (-((N : ℂ) * ((φ : ℂ) * Complex.I))) = 1)
    {q : Fin N → ℝ} (hq : angularShortSquare q ≤ s) (hne : d.pole q ≠ 0) :
    d.actualResidue q = -(d.pole q) *
      (realNegativeDensity b B φ N 0 q - d.realCycleRemainderDensity hs 0 q) := by
  have he := d.exact_density hres ⟨q, hq⟩ 0
    (Metric.mem_ball_self (div_pos hr (Nat.cast_pos.mpr hN))) (Ne.symm hne)
  rw [d.realCycleRemainderDensity_eq hs hq]
  change realNegativeDensity b B φ N 0 q =
    d.actualResidue q / (0 - d.pole q) + d.remainder 0 ⟨q, hq⟩ at he
  rw [he]
  field_simp
  ring

end InnerRemainderFamily

def innerCyclePoleIntegral {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (t : ℂ) : ℂ :=
  ∫ q in regularAngularBox n,
    if angularShortSquare (negativeConstrainedAngles q) ≤ s then
      d.actualResidue (negativeConstrainedAngles q) / (t - d.pole (negativeConstrainedAngles q)) else 0

def innerCyclePoleCoefficient {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (j : ℕ) : ℂ :=
  -(∫ q in regularAngularBox n,
    if angularShortSquare (negativeConstrainedAngles q) ≤ s then
      d.actualResidue (negativeConstrainedAngles q) / (d.pole (negativeConstrainedAngles q)) ^ (j + 1) else 0)

theorem continuousOn_real_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → ℂ} {g : X → Y} {K : Set Y}
    (hf : ContinuousOn f K) (hg : Continuous g) :
    ContinuousOn (fun x => f (g x)) (g ⁻¹' K) :=
  hf.comp hg.continuousOn (fun _ hx => hx)

theorem measurable_real_pullback {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : Y → ℂ} {g : X → Y} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f (g x)) := hf.comp hg

theorem measurable_complex_parameter_slice {X : Type*} [MeasurableSpace X]
    {F : ℂ → X → ℂ} (hF : Measurable (Function.uncurry F)) (t : ℂ) :
    Measurable (F t) := hF.comp (f := fun x : X => (t, x)) (measurable_const.prodMk measurable_id)

set_option maxHeartbeats 1000000 in
theorem exists_inner_cycle_pole_representatives {b B : ℂ → ℂ} {φ r s M kappa c E : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hr : 0 < r) (hs : 0 ≤ s) (hM : 0 ≤ M) (hc : 0 < c) (hE : 0 ≤ E)
    (hres : Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1)
    (hmeas : Measurable (realNegativeDensity b B φ (n + 1) 0))
    (hbound : ∀ q : Fin n → ℝ, ‖realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q)‖ ≤ E)
    (hsep : ∀ q : Fin n → ℝ, angularShortSquare (negativeConstrainedAngles q) ≤ s →
      c ≤ ‖d.pole (negativeConstrainedAngles q)‖) :
    ∃ A P : (Fin n → ℝ) → ℂ, ∃ L : ℝ, 0 < L ∧ Measurable A ∧ Measurable P ∧
      (∀ q, ‖A q‖ ≤ L) ∧ (∀ q, c ≤ ‖P q‖) ∧
      (∀ q, angularShortSquare (negativeConstrainedAngles q) ≤ s →
        A q = d.actualResidue (negativeConstrainedAngles q) ∧ P q = d.pole (negativeConstrainedAngles q)) ∧
      ∀ q, ¬angularShortSquare (negativeConstrainedAngles q) ≤ s → A q = 0 := by
  let K : Set (Fin n → ℝ) := {q | angularShortSquare (negativeConstrainedAngles q) ≤ s}
  let P : (Fin n → ℝ) → ℂ := fun q =>
    if q ∈ K then d.pole (negativeConstrainedAngles q) else ((c + 1 : ℝ) : ℂ)
  let A : (Fin n → ℝ) → ℂ := fun q => if q ∈ K then d.actualResidue (negativeConstrainedAngles q) else 0
  let Erem : ℝ := M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / ‖windingNormalization (n + 1)‖
  let L : ℝ := 1 + (r / (4 * (n + 1 : ℕ))) * (E + Erem)
  have hL : 0 < L := by dsimp [L, Erem]; positivity
  have hK : MeasurableSet K :=
    (isClosed_le ((angularShortSquare_continuous (n + 1)).comp
      (negativeConstrainedAngles_continuous n)) continuous_const).measurableSet
  have hPc : ContinuousOn (fun q : Fin n → ℝ => d.pole (negativeConstrainedAngles q)) K := by
    change ContinuousOn (fun q : Fin n → ℝ => d.pole (negativeConstrainedAngles q))
      (negativeConstrainedAngles ⁻¹' {q | angularShortSquare q ≤ s})
    exact continuousOn_real_preimage d.pole_continuous (negativeConstrainedAngles_continuous n)
  have hPm : Measurable P :=
    hPc.measurable_piecewise (continuousOn_const (c := ((c + 1 : ℝ) : ℂ))) hK
  have hF : Measurable (fun q : Fin n → ℝ =>
      if q ∈ K then realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q) else 0) :=
    Measurable.ite hK (measurable_real_pullback hmeas (negativeConstrainedAngles_continuous n).measurable)
      measurable_const
  have hG0 : Measurable (d.realCycleRemainderDensity hs 0) :=
    measurable_complex_parameter_slice (d.realCycleRemainderDensity_measurable hs) 0
  have hG : Measurable (fun q : Fin n → ℝ =>
      d.realCycleRemainderDensity hs 0 (negativeConstrainedAngles q)) :=
    measurable_real_pullback hG0 (negativeConstrainedAngles_continuous n).measurable
  have hAeq (q : Fin n → ℝ) : A q = -P q *
      ((if q ∈ K then realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q) else 0) -
        d.realCycleRemainderDensity hs 0 (negativeConstrainedAngles q)) := by
    by_cases hq : q ∈ K
    · simp only [A, P, hq, ↓reduceIte]
      exact d.residue_from_center hr hs (Nat.succ_pos n) hres hq
        (norm_pos_iff.mp (hc.trans_le (hsep q hq)))
    · have hq' : ¬ angularShortSquare (negativeConstrainedAngles q) ≤ s := hq
      simp only [A, P, hq, ↓reduceIte, InnerRemainderFamily.realCycleRemainderDensity,
        hq', sub_self, mul_zero]
  have hAm : Measurable A := by
    rw [show A = (fun q => -P q *
      ((if q ∈ K then realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q) else 0) -
        d.realCycleRemainderDensity hs 0 (negativeConstrainedAngles q))) from funext hAeq]
    exact hPm.neg.mul (hF.sub hG)
  refine ⟨A, P, L, hL, hAm, hPm, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ K
    · rw [hAeq, norm_mul, norm_neg]
      have hPq : ‖P q‖ ≤ r / (4 * (n + 1 : ℕ)) := by
        simpa only [P, hq, ↓reduceIte] using d.pole_bound ⟨negativeConstrainedAngles q, hq⟩
      have hGq : ‖d.realCycleRemainderDensity hs 0 (negativeConstrainedAngles q)‖ ≤ Erem :=
        d.realCycleRemainderDensity_bound hs hM _ (Metric.mem_ball_self (by positivity))
      have hdiff : ‖(if q ∈ K then realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q) else 0) -
          d.realCycleRemainderDensity hs 0 (negativeConstrainedAngles q)‖ ≤ E + Erem := by
        simp only [hq, ↓reduceIte]
        exact (norm_sub_le _ _).trans (add_le_add (hbound q) hGq)
      exact (mul_le_mul hPq hdiff (norm_nonneg _) (by positivity)).trans (by dsimp [L]; linarith)
    · simpa only [A, hq, ↓reduceIte, norm_zero] using hL.le
  · intro q
    by_cases hq : q ∈ K
    · simpa only [P, hq, ↓reduceIte] using hsep q hq
    · simp only [P, hq, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < c + 1)]
      linarith
  · intro q hq
    exact ⟨by simp only [A, K, Set.mem_ofPred_eq, hq, ↓reduceIte],
      by simp only [P, K, Set.mem_ofPred_eq, hq, ↓reduceIte]⟩
  · intro q hq
    simp only [A, K, Set.mem_ofPred_eq, hq, ↓reduceIte]

end
end IsingBulk.AnisoF002.NegativeHT

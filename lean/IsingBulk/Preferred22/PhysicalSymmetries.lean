import IsingBulk.Preferred22.PhysicalKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Reflection and complex conjugation for the actual constrained coefficients. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set

theorem gaugeKernel_det_conj {N : ℕ} (hN : Even N) (y z : Fin N → ℂ) :
    (gaugeKernel (fun i => star (y i)) (fun i => star (z i))).det =
      star ((gaugeKernel y z).det) := by
  have hr : rationalKernel (fun i => star (y i)) (fun i => star (z i)) =
      (starRingEnd ℂ).mapMatrix (rationalKernel y z) := by
    ext i j
    simp [rationalKernel]
  rw [gaugeKernel_det_normalization, gaugeKernel_det_normalization, hr,
    ← RingHom.map_det]
  simp [hN.neg_pow]

theorem angularRoots_conj {N : ℕ} {s : ℂ} (hs : 1 < ‖s‖) (θ : Fin N → ℝ) :
    angularRoots (star s) (-θ) = fun i => star (angularRoots s θ i) := by
  funext i
  have hW : angularW (star s) ((-θ) i) = star (angularW s (θ i)) := by
    simp only [angularW, temperatureTrace, Pi.neg_apply, Real.cos_neg,
      star_add, star_sub, Complex.star_def, Complex.conj_ofReal, map_inv₀]
  dsimp only [angularRoots]
  rw [hW, physicalRoot_conj (angularW_off_segment hs (θ i))]

theorem oneBody_conj (z : ℂ) : oneBody (star z) = star (oneBody z) := by
  simp [oneBody]

theorem fullAngularDensity_conj {N : ℕ} (hN : Even N) {s : ℂ} (hs : 1 < ‖s‖)
    (θ : Fin N → ℝ) : fullAngularDensity (star s) (-θ) = star (fullAngularDensity s θ) := by
  have hy : (fun i => angleRoot ((-θ) i)) = fun i => star (angleRoot (θ i)) := by
    funext i
    exact angleRoot_neg (θ i)
  simp only [fullAngularDensity, angularRoots_conj hs θ, hy, gaugeKernel_det_conj hN,
    oneBody_conj]
  simp

theorem constrainedAngles_neg {n : ℕ} (θ : Fin n → ℝ) : constrainedAngles (-θ) = -constrainedAngles θ := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [constrainedAngles]
  · simp [constrainedAngles]

/-- Reflection preserves the exact N-dimensional Ioc box integral; endpoint
sets are removed by a proved almost-everywhere equality with the closed box. -/
theorem angularBox_integral_neg {n : ℕ} (f : (Fin n → ℝ) → ℂ) :
    (∫ θ in angularBox n, f (-θ)) = ∫ θ in angularBox n, f θ := by
  let B : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-Real.pi) Real.pi)
  have hB : angularBox n =ᵐ[volume] B := by
    exact Measure.pi_Ioc_ae_eq_pi_Icc
  have hpre : (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' B = B := by
    ext θ
    simp only [B, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Icc, Pi.neg_apply]
    constructor <;> intro h i <;> obtain ⟨h1,h2⟩ := h i <;> constructor <;> linarith
  rw [setIntegral_congr_set hB, setIntegral_congr_set hB]
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))).setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin n → ℝ)).measurableEmbedding f B
  rwa [hpre] at h

/-- The exact constrained coefficient commutes with conjugation, at every
positive even order. This statement does not presume summability of the series. -/
theorem coefficient_conj {N : ℕ} (hN : Even N) {s : ℂ} (hs : 1 < ‖s‖) :
    coefficient N (star s) = star (coefficient N s) := by
  cases N with
  | zero => simp [coefficient]
  | succ n =>
    simp only [coefficient]
    rw [← angularBox_integral_neg (fun θ : Fin n → ℝ =>
      fullAngularDensity (star s) (constrainedAngles θ))]
    simp_rw [constrainedAngles_neg, fullAngularDensity_conj hN hs]
    simp only [Complex.star_def]
    rw [integral_conj]
    simp [map_ofNat]

theorem evenSeries_conj {s : ℂ} (hs : 1 < ‖s‖) : evenSeries (star s) = star (evenSeries s) := by
  unfold evenSeries
  simp_rw [coefficient_conj (even_two_mul _) hs]
  exact tsum_star.symm

end
end IsingBulk.Preferred22

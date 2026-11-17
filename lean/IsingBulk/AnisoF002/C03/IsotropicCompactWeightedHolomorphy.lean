import IsingBulk.AnisoF002.C03.IsotropicCompactParticleHolomorphy

/-!
# Arbitrary continuous compact angular weights in actual centered integrals

The weight need only be continuous and supported in a finite real
rectangle. The original complete normalized physical density and actual
balanced Jacobian are unchanged. Compactness constructs a common local
parameter disk, proves every derivative integrable, and justifies every
order of differentiation on the whole independent-coordinate space.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

def centeredWeightedPhysicalCoefficient {n : ℕ} (η τ ξ μ : ℝ) (σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (S : ℂ) : ℂ :=
  ∫ x : Fin n → ℝ, g (centeredConstraintAngles μ x) *
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, centeredConstraintAngles μ x)

theorem centered_rectangular_weight_zero_off_box {n : ℕ} {L U μ : ℝ}
    {g : (Fin (n + 1) → ℝ) → ℂ}
    (hg : Function.support g ⊆ Icc (fun _ => L) (fun _ => U))
    {x : Fin n → ℝ} (hx : x ∉ Icc (fun _ => L - μ) (fun _ => U - μ)) :
    g (centeredConstraintAngles μ x) = 0 := by
  by_contra hn
  have hh := hg hn
  apply hx
  constructor
  · intro i
    have hi := hh.1 i.castSucc
    simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc] at hi
    linarith
  · intro i
    have hi := hh.2 i.castSucc
    simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc] at hi
    linarith

theorem centeredWeightedPhysicalCoefficient_analytic_and_jets {n : ℕ}
    (η τ ξ μ : ℝ) (σ : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : Continuous g) {L U : ℝ}
    (hsupp : Function.support g ⊆ Icc (fun _ => L) (fun _ => U))
    (S : ℂ) (hS : 0 < S.im) :
    AnalyticAt ℂ (centeredWeightedPhysicalCoefficient η τ ξ μ σ g) S ∧
      ∀ j : ℕ,
        Integrable (fun x : Fin n → ℝ => iteratedDeriv j (fun T =>
          g (centeredConstraintAngles μ x) *
            homotopyPulledDensity η τ (isotropicBarePhysicalDensity T σ)
              (ξ, centeredConstraintAngles μ x)) S) ∧
        iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ g) S =
          ∫ x : Fin n → ℝ, iteratedDeriv j (fun T => g (centeredConstraintAngles μ x) *
            homotopyPulledDensity η τ (isotropicBarePhysicalDensity T σ)
              (ξ, centeredConstraintAngles μ x)) S := by
  let K := Icc (fun _ : Fin n => L - μ) (fun _ => U - μ)
  let H : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) := fun x =>
    (g (centeredConstraintAngles μ x) * (actualBalancedJacobian η τ ξ (centeredConstraintAngles μ x)).det,
      actualHomotopyAngle η τ ξ (centeredConstraintAngles μ x))
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hH : Continuous H := ((hg.mul (actualBalancedJacobian_det_continuous η τ ξ)).prodMk
    (actualHomotopyAngles_continuous η τ ξ)).comp (centeredConstraintAngles_continuous μ)
  have hzero (x : Fin n → ℝ) (hx : x ∉ K) : g (centeredConstraintAngles μ x) = 0 :=
    centered_rectangular_weight_zero_off_box hsupp hx
  have hfamily (T : ℂ) (x : Fin n → ℝ) : mixedPhysicalAnalyticFamily σ (T, H x) =
      g (centeredConstraintAngles μ x) * homotopyPulledDensity η τ
        (isotropicBarePhysicalDensity T σ) (ξ, centeredConstraintAngles μ x) := by
    simp only [mixedPhysicalAnalyticFamily, H, homotopyPulledDensity_actual, mul_assoc]
  have he : centeredWeightedPhysicalCoefficient η τ ξ μ σ g =
      fun T => ∫ x, mixedPhysicalAnalyticFamily σ (T, H x) ∂volume.restrict K := by
    funext T
    simp only [hfamily]
    unfold centeredWeightedPhysicalCoefficient
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hzero x hx, zero_mul]
  have ha (x : Fin n → ℝ) (_ : x ∈ K) :
      AnalyticAt ℂ (mixedPhysicalAnalyticFamily σ) (S, H x) :=
    mixedPhysicalAnalyticFamily_analyticAt (by omega) hσ (S, H x)
      (fun i => actual_balanced_homotopy_sheet S hS η τ ξ hη hτ hξ (centeredConstraintAngles μ x) i)
  refine ⟨?_, ?_⟩
  · rw [he]
    exact analyticAt_integral_of_joint_analytic hK (ae_restrict_mem measurableSet_Icc) hH ha
  · intro j
    have hjzero (x : Fin n → ℝ) (hx : x ∉ K) :
        iteratedDeriv j (fun T => mixedPhysicalAnalyticFamily σ (T, H x)) S = 0 := by
      have hh : (fun T => mixedPhysicalAnalyticFamily σ (T, H x)) = fun _ => 0 := by
        funext T
        rw [hfamily, hzero x hx, zero_mul]
      rw [hh]
      simp
    have hjcont : ContinuousOn (fun x : Fin n → ℝ =>
        iteratedDeriv j (fun T => mixedPhysicalAnalyticFamily σ (T, H x)) S) K := by
      intro x hx
      exact ((parameterIteratedDeriv_analyticAt (ha x hx) j).continuousAt.comp
        (f := fun y : Fin n → ℝ => (S, H y))
        (continuousAt_const.prodMk hH.continuousAt)).continuousWithinAt
    have hjsupp : Function.support (fun x : Fin n → ℝ =>
        iteratedDeriv j (fun T => mixedPhysicalAnalyticFamily σ (T, H x)) S) ⊆ K := by
      intro x hx
      by_contra hn
      exact hx (hjzero x hn)
    have hji := (integrableOn_iff_integrable_of_support_subset (μ := volume) hjsupp).mp
      (hjcont.integrableOn_compact (μ := volume) hK)
    have hje := iteratedDeriv_integral_of_joint_analytic (μ := volume.restrict K)
      hK (ae_restrict_mem measurableSet_Icc) hH ha j
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hjzero] at hje
    constructor
    · simpa only [hfamily] using hji
    · rw [he]
      simpa only [hfamily] using hje

end IsingBulk.AnisoF002.Isotropic

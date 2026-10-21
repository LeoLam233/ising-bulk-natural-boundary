import IsingBulk.HT.Contour.SignedChartBridge
import IsingBulk.Tail.MicrocoreDensityAllOrder

/-! The reflected odd source has plus product kernels. Its complete pair
zeros remain in one frozen Vandermonde factor at every Lie order. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Jets IsingBulk.Lie
open scoped BigOperators ContDiff

abbrev negativeMicroRegularDensity {N : ℕ} : ℂ → (Fin N → ℂ) → ℂ :=
  signedMicroRegularDensity (-1)
abbrev negativeSourceAngularDensity {N : ℕ} : ℝ → ℂ → (Fin N → ℝ) → ℂ :=
  signedSourceAngularDensity (-1)
abbrev negativePulledDensity {N : ℕ} := @signedPulledDensity N (-1)

def negativeMicrocoreVariableFactor {N : ℕ} (z : ℂ × (Fin N → ℂ)) : ℂ :=
  microRegularAmplitude z.1 z.2/(1+regularYProduct z.1 z.2)

def negativeMicrocorePhaseFactor {N : ℕ} (φ : Fin N → ℂ) : ℂ :=
  microcoreVandermondeSquared φ/(1+Complex.exp (-Complex.I*∑ i,φ i))

theorem negativeMicrocorePhaseFactor_differentiable {N : ℕ} (φ : Fin N → ℂ)
    (hZ : 1+Complex.exp (-Complex.I*∑ i,φ i) ≠ 0) :
    DifferentiableAt ℂ negativeMicrocorePhaseFactor φ := by
  unfold negativeMicrocorePhaseFactor
  have hP : DifferentiableAt ℂ (@microcoreVandermondeSquared N) φ :=
    microcoreVandermondeSquared_differentiable N φ
  have hD : DifferentiableAt ℂ (fun ψ : Fin N → ℂ =>
      1+Complex.exp (-Complex.I*∑ i,ψ i)) φ := by fun_prop
  convert! hP.mul (hD.inv hZ) using 1

theorem negativeMicroRegularDensity_phase_factor {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) :
    negativeMicroRegularDensity s φ =
      negativeMicrocorePhaseFactor φ*negativeMicrocoreVariableFactor (s,φ) := by
  rw [negativeMicroRegularDensity,signedMicroRegularDensity_unfactored]
  simp only [neg_one_mul,sub_neg_eq_add]
  unfold negativeMicrocorePhaseFactor negativeMicrocoreVariableFactor regularZProduct
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem negative_microcore_weighted_density_factor {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ) :
    (fun s x => (w x:ℂ)*chartPullback v θ (@negativeMicroRegularDensity (n+1)) s x) =
      (fun s x => negativeMicrocorePhaseFactor (chartMap v θ s x)*
        ((w x:ℂ)*chartPullback v θ (fun t φ => negativeMicrocoreVariableFactor (t,φ)) s x)) := by
  funext s x
  simp only [chartPullback,negativeMicroRegularDensity_phase_factor]
  change (w x:ℂ)*(chartJacobian v θ s x*(negativeMicrocorePhaseFactor (chartMap v θ s x)*
    negativeMicrocoreVariableFactor (s,chartMap v θ s x))) =
      negativeMicrocorePhaseFactor (chartMap v θ s x)*((w x:ℂ)*(chartJacobian v θ s x*
        negativeMicrocoreVariableFactor (s,chartMap v θ s x)))
  ring

theorem negative_microcore_density_all_order {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hw : ContDiff ℝ ∞ w) (hchart : ∀ s ∈ U, ∀ x ∈ R, MicrocoreJetPoint v θ s x)
    (hF : ∀ s ∈ U, ∀ x ∈ R,
      AnalyticAt ℂ negativeMicrocoreVariableFactor (s,chartMap v θ s x))
    (hZ : ∀ s ∈ U, ∀ x ∈ R,1+regularZProduct s (chartMap v θ s x) ≠ 0) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (microcoreField v θ))^[j]
        (fun t y => (w y:ℂ)*chartPullback v θ (@negativeMicroRegularDensity (n+1)) t y)) s x =
      negativeMicrocorePhaseFactor (chartMap v θ s x)*
        microcoreTermSum v θ w negativeMicrocoreVariableFactor j s x := by
  rw [negative_microcore_weighted_density_factor]
  exact microcore_frozen_factor_all_order v θ w negativeMicrocoreVariableFactor
    negativeMicrocorePhaseFactor U R hU hR hw hchart hF
    (fun s hs x hx => negativeMicrocorePhaseFactor_differentiable _ (hZ s hs x hx)) j

theorem negative_micro_original_density_regular {n : ℕ} (s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hv : v < 0)
    (hg : ∀ i,0 < (angularG v θ (x i)).re)
    (hi : ∀ i,0 < (chartW s v θ (x i)).im) :
    chartPullback v θ (@negativeMicroRegularDensity (n+1)) s x =
      negativeSourceAngularDensity (Real.exp v) s (fun i => x i-θ) :=
  signed_micro_original_density_regular (-1) s v θ x hv hg hi

theorem negativeSourceAngularDensity_all_period {N : ℕ} (r : ℝ) (s : ℂ)
    (θ : Fin N → ℝ) :
    negativeSourceAngularDensity r s (fun i => θ i+2*Real.pi)=
      negativeSourceAngularDensity r s θ := by
  have hy : IsingBulk.First.angleTuple r (fun i => θ i+2*Real.pi)=IsingBulk.First.angleTuple r θ := by
    funext i
    exact IsingBulk.First.anglePoint_add_period r (θ i)
  simp only [negativeSourceAngularDensity,signedSourceAngularDensity,
    IsingBulk.First.angleProductJacobian,IsingBulk.First.angleJacobian,
    IsingBulk.First.anglePoint_add_period,hy]

end
end IsingBulk.HT.Tail

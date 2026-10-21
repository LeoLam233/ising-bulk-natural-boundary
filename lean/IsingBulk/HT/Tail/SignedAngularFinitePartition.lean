import IsingBulk.HT.Contour.SignedRetraction
import IsingBulk.HT.Contour.SignedOriginalHolomorphy
import IsingBulk.Tail.AngularFinitePartition

/-! Finite continuous angular partitions of the actual homotopy density. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.First MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

def signedWeightedAngularIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r tau lam : ℝ)
    (w : (Fin N → ℝ) → ℂ) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N, w theta*signedPulledDensity σ f r tau lam s theta

theorem signed_weightedAngularIntegral_finite_partition {I : Type*} [Fintype I]
    (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r tau lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (w : (Fin N → ℝ) → ℂ) (hw : Continuous w)
    (v : I → (Fin N → ℝ) → ℂ) (hv : ∀ i, Continuous (v i))
    (hpart : ∀ theta, ∑ i, v i theta = 1) (s : ℂ) (hs : s ∈ dampingDomain r) :
    signedWeightedAngularIntegral σ N f r tau lam w s =
      ∑ i, signedWeightedAngularIntegral σ N f r tau lam (fun theta => w theta*v i theta) s := by
  have hd := (signed_fixedDensity_contDiff σ hσ hN f hf hr hr1 htau hlam s hs.2).continuous
  have hint (i : I) : IntegrableOn (fun theta => w theta*v i theta*signedPulledDensity σ f r tau lam s theta)
      (angleBox N) := ((hw.mul (hv i)).mul hd).continuousOn.integrableOn_compact isCompact_Icc
  unfold signedWeightedAngularIntegral
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta _
  dsimp only
  rw [← Finset.sum_mul,← Finset.mul_sum,hpart,mul_one]

theorem signed_weightedAngularIntegral_finite_partition_jets {I : Type*} [Fintype I]
    (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r tau lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (w : (Fin N → ℝ) → ℂ) (hw : Continuous w)
    (v : I → (Fin N → ℝ) → ℂ) (hv : ∀ i, Continuous (v i))
    (hpart : ∀ theta, ∑ i, v i theta = 1) (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedWeightedAngularIntegral σ N f r tau lam w) s =
      ∑ i, iteratedDeriv j (signedWeightedAngularIntegral σ N f r tau lam (fun theta => w theta*v i theta)) s := by
  have he : signedWeightedAngularIntegral σ N f r tau lam w =ᶠ[𝓝 s]
      (fun z => ∑ i, signedWeightedAngularIntegral σ N f r tau lam (fun theta => w theta*v i theta) z) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    exact signed_weightedAngularIntegral_finite_partition σ hσ N hN f hf hr hr1 htau hlam w hw v hv hpart z hz
  rw [he.iteratedDeriv_eq j]
  exact iteratedDeriv_fun_sum (fun i _ =>
    (signed_weighted_homotopy_slice_analytic σ hσ N hN f hf hr hr1 htau hlam _ (hw.mul (hv i)) s hs).contDiffAt)

end
end IsingBulk.HT.Tail

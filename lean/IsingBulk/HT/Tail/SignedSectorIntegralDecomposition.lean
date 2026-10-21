import IsingBulk.Tail.SectorIntegralDecomposition
import IsingBulk.HT.Contour.SignedOriginalHolomorphy
import IsingBulk.HT.Contour.SignedRetraction
import IsingBulk.HT.Tail.SignedCurrentDerivatives

/-! Exact fixed-weight finite sector decomposition of the actual signed
source, with all complex parameter derivatives and no sector estimate input. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

def signedSectorWeightedIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r tau lam : ℝ)
    (weight : (Fin N → ℝ) → ℂ) (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N,
    weight theta*(sectorPartitionWeight b outer inner ho hi label theta:ℂ)*signedPulledDensity σ f r tau lam s theta

theorem signed_sectorWeightedIntegral_sum (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hw : Continuous weight)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) :
    (∫ theta in angleBox N, weight theta*signedPulledDensity σ f r tau lam s theta) =
      ∑ label, signedSectorWeightedIntegral σ N f r tau lam weight b outer inner ho hi label s := by
  have hd := (signed_fixedDensity_contDiff σ hσ hN f hf hr hr1 htau hlam s hs.2).continuous
  have hi' (label : Option (Fin N × (Fin N → Fin 3))) :
      IntegrableOn (fun theta => weight theta*(sectorPartitionWeight b outer inner ho hi label theta:ℂ)*
        signedPulledDensity σ f r tau lam s theta) (angleBox N) := by
    have hc := ((hw.mul (Complex.continuous_ofReal.comp
      (sectorPartitionWeight_smooth b outer inner ho hi label).continuous)).mul hd)
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  unfold signedSectorWeightedIntegral
  rw [← integral_finsetSum _ (fun label _ => hi' label)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta _
  dsimp only
  rw [← Finset.sum_mul,← Finset.mul_sum,← Complex.ofReal_sum,sectorPartitionWeight_sum,Complex.ofReal_one,mul_one]

theorem signed_sectorWeightedIntegral_iteratedDeriv (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hw : Continuous weight)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (fun z => ∫ theta in angleBox N, weight theta*signedPulledDensity σ f r tau lam z theta) s =
      ∑ label, iteratedDeriv j (signedSectorWeightedIntegral σ N f r tau lam weight b outer inner ho hi label) s := by
  have he : (fun z => ∫ theta in angleBox N, weight theta*signedPulledDensity σ f r tau lam z theta) =ᶠ[𝓝 s]
      (fun z => ∑ label, signedSectorWeightedIntegral σ N f r tau lam weight b outer inner ho hi label z) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    exact signed_sectorWeightedIntegral_sum σ hσ N hN f hf hr hr1 htau hlam weight hw b outer inner ho hi z hz
  rw [he.iteratedDeriv_eq j]
  apply iteratedDeriv_fun_sum
  intro label _
  have hweight := hw.mul (Complex.continuous_ofReal.comp
    (sectorPartitionWeight_smooth b outer inner ho hi label).continuous)
  exact (signed_weighted_homotopy_slice_analytic σ hσ N hN f hf hr hr1 htau hlam _ hweight s hs).contDiffAt


def signedOriginalSectorIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r tau : ℝ)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) : ℂ → ℂ :=
  signedSectorWeightedIntegral σ N f r tau 0 (fun theta => (angularSelector f theta:ℂ)) b outer inner ho hi label

theorem signed_originalLower_sector_derivative (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedOriginalLowerIntegral σ N f r tau) s =
      ∑ label, iteratedDeriv j (signedOriginalSectorIntegral σ N f r tau b outer inner ho hi label) s :=
  signed_sectorWeightedIntegral_iteratedDeriv σ hσ N hN f hf hr hr1 htau le_rfl _
    (complexSelector_contDiff f hf).continuous b outer inner ho hi s hs j

def signedCurrentSectorIntegral (σ : ℂ) (N : ℕ) (f : SelectorFunctions) (r tau lam : ℝ) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) : ℂ → ℂ :=
  signedSectorWeightedIntegral σ N f r tau lam (namedCurrentMultiplier f tau q) b outer inner ho hi label

theorem signed_namedCurrent_sector_derivative (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedActualNamedCurrentIntegral σ N f r tau lam q) s =
      ∑ label, iteratedDeriv j (signedCurrentSectorIntegral σ N f r tau lam q b outer inner ho hi label) s :=
  signed_sectorWeightedIntegral_iteratedDeriv σ hσ N hN f hf hr hr1 htau hlam _
    (namedCurrentMultiplier_continuous f hf tau q) b outer inner ho hi s hs j

end
end IsingBulk.HT.Tail

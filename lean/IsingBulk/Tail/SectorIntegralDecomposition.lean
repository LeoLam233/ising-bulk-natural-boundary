import IsingBulk.Tail.NestedSectorPartition
import IsingBulk.Tail.SelectorDerivativeDistribution

/-! Exact finite fixed-weight sector decomposition of the literal angular
integral, including all fixed parameter derivatives on the actual domain. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

def sectorPartitionWeight {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) (theta : Fin N → ℝ) : ℝ :=
  match label with
  | none => ∏ i, sectorBranch b outer ho (theta i)
  | some (q,sigma) => nestedSectorWeight b outer inner ho hi q sigma theta

theorem sectorPartitionWeight_sum {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (theta : Fin N → ℝ) :
    ∑ label : Option (Fin N × (Fin N → Fin 3)), sectorPartitionWeight b outer inner ho hi label theta = 1 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  exact nested_sector_partition b outer inner ho hi theta

theorem sectorPartitionWeight_smooth {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) :
    ContDiff ℝ ∞ (sectorPartitionWeight b outer inner ho hi label) := by
  cases label with
  | none => exact contDiff_prod (fun i _ => (sector_labels_smooth b outer ho).2.2.comp (contDiff_apply ℝ ℝ i))
  | some label =>
    exact (sectorOuterAnchor_smooth b outer ho label.1).mul
      (sector_assignment_smooth b inner hi label.2)

def sectorWeightedIntegral (N : ℕ) (f : SelectorFunctions) (r tau lam : ℝ)
    (weight : (Fin N → ℝ) → ℂ) (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N,
    weight theta*(sectorPartitionWeight b outer inner ho hi label theta:ℂ)*pulledDensity f r tau lam s theta

theorem sectorWeightedIntegral_sum (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hw : Continuous weight)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) :
    (∫ theta in angleBox N, weight theta*pulledDensity f r tau lam s theta) =
      ∑ label, sectorWeightedIntegral N f r tau lam weight b outer inner ho hi label s := by
  have hd := (fixedDensity_contDiff hN f hf hr hr1 htau hlam s hs.2).continuous
  have hi' (label : Option (Fin N × (Fin N → Fin 3))) :
      IntegrableOn (fun theta => weight theta*(sectorPartitionWeight b outer inner ho hi label theta:ℂ)*
        pulledDensity f r tau lam s theta) (angleBox N) := by
    have hc := ((hw.mul (Complex.continuous_ofReal.comp
      (sectorPartitionWeight_smooth b outer inner ho hi label).continuous)).mul hd)
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  unfold sectorWeightedIntegral
  rw [← integral_finsetSum _ (fun label _ => hi' label)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta _
  dsimp only
  rw [← Finset.sum_mul,← Finset.mul_sum,← Complex.ofReal_sum,sectorPartitionWeight_sum,Complex.ofReal_one,mul_one]

theorem sectorWeightedIntegral_iteratedDeriv (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hw : Continuous weight)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (fun z => ∫ theta in angleBox N, weight theta*pulledDensity f r tau lam z theta) s =
      ∑ label, iteratedDeriv j (sectorWeightedIntegral N f r tau lam weight b outer inner ho hi label) s := by
  have he : (fun z => ∫ theta in angleBox N, weight theta*pulledDensity f r tau lam z theta) =ᶠ[𝓝 s]
      (fun z => ∑ label, sectorWeightedIntegral N f r tau lam weight b outer inner ho hi label z) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    exact sectorWeightedIntegral_sum N hN f hf hr hr1 htau hlam weight hw b outer inner ho hi z hz
  rw [he.iteratedDeriv_eq j]
  apply iteratedDeriv_fun_sum
  intro label _
  have hweight := hw.mul (Complex.continuous_ofReal.comp
    (sectorPartitionWeight_smooth b outer inner ho hi label).continuous)
  exact (weighted_homotopy_slice_analytic N hN f hf hr hr1 htau hlam _ hweight s hs).contDiffAt


def originalSectorIntegral (N : ℕ) (f : SelectorFunctions) (r tau : ℝ)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) : ℂ → ℂ :=
  sectorWeightedIntegral N f r tau 0 (fun theta => (angularSelector f theta:ℂ)) b outer inner ho hi label

theorem originalLower_sector_derivative (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (originalLowerIntegral N f r tau) s =
      ∑ label, iteratedDeriv j (originalSectorIntegral N f r tau b outer inner ho hi label) s :=
  sectorWeightedIntegral_iteratedDeriv N hN f hf hr hr1 htau le_rfl _
    (complexSelector_contDiff f hf).continuous b outer inner ho hi s hs j

def namedCurrentMultiplier {N : ℕ} (f : SelectorFunctions) (tau : ℝ)
    (q : Fin N) (theta : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(tau:ℂ)*(namedSelectorDerivative f q theta:ℂ)

theorem namedCurrentMultiplier_continuous {N : ℕ} (f : SelectorFunctions)
    (hf : RegularSelector f) (tau : ℝ) (q : Fin N) :
    Continuous (namedCurrentMultiplier f tau q) := by
  have had : ContDiff ℝ ∞ (deriv f.a) := by apply ContDiff.deriv'; simpa using hf.a_smooth
  have hda := had.continuous
  have ha := hf.a_smooth.continuous
  unfold namedCurrentMultiplier namedSelectorDerivative
  fun_prop

def currentSectorIntegral (N : ℕ) (f : SelectorFunctions) (r tau lam : ℝ) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) : ℂ → ℂ :=
  sectorWeightedIntegral N f r tau lam (namedCurrentMultiplier f tau q) b outer inner ho hi label

theorem namedCurrent_sector_derivative (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (actualNamedCurrentIntegral N f r tau lam q) s =
      ∑ label, iteratedDeriv j (currentSectorIntegral N f r tau lam q b outer inner ho hi label) s :=
  sectorWeightedIntegral_iteratedDeriv N hN f hf hr hr1 htau hlam _
    (namedCurrentMultiplier_continuous f hf tau q) b outer inner ho hi s hs j

end
end IsingBulk.Tail

import IsingBulk.Tail.CompactSignedLocalization

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology

theorem original_sector_compact_integral_jets {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (J : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv J (originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma))) s=
      iteratedDeriv J (fun z => ∫ θ,
        compactSignedWeight (originalSectorAngularWeight f b outer inner ho hi q sigma) θ*
          pulledDensity f r τ 0 z θ) s := by
  have he : originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma)) =ᶠ[𝓝 s]
      (fun z => ∫ θ, compactSignedWeight (originalSectorAngularWeight f b outer inner ho hi q sigma) θ*
        pulledDensity f r τ 0 z θ) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    rw [compactSignedWeight_integral]
    simpa only [iteratedDeriv_zero] using original_sector_signed_jets N hN f hf hr hr1 hτ
      b outer inner ho hi q sigma z hz 0
  exact he.iteratedDeriv_eq J

theorem current_sector_compact_integral_jets {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (qS : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (J : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv J (currentSectorIntegral N f r τ lam qS b outer inner ho hi (some (q,sigma))) s=
      iteratedDeriv J (fun z => ∫ θ,
        compactSignedWeight (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) θ*
          pulledDensity f r τ lam z θ) s := by
  have he : currentSectorIntegral N f r τ lam qS b outer inner ho hi (some (q,sigma)) =ᶠ[𝓝 s]
      (fun z => ∫ θ, compactSignedWeight (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) θ*
        pulledDensity f r τ lam z θ) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    rw [compactSignedWeight_integral]
    simpa only [iteratedDeriv_zero] using current_sector_signed_jets N hN f hf hr hr1 hτ hlam qS
      b outer inner ho hi q sigma z hz 0
  exact he.iteratedDeriv_eq J

end
end IsingBulk.Tail

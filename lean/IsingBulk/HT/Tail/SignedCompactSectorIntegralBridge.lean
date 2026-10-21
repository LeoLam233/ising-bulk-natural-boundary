import IsingBulk.Tail.CompactSectorIntegralBridge
import IsingBulk.HT.Tail.SignedSectorIntegralDecomposition

/-! Exact transfer from the periodic angular cube to the compact signed
fundamental domain, for the physical signed kernel and every parameter jet.
The word `Signed` in LT `compactSignedWeight` denotes the angle interval;
it does not change the global denominator. Both operations are explicit here. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology

theorem signedPulledDensity_periodic (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    (hf : RegularSelector f) (r τ lam : ℝ) (s : ℂ) :
    CoordinatePeriodic N (signedPulledDensity σ f r τ lam s) := by
  intro θ q
  unfold signedPulledDensity
  rw [angularJacobian_periodic f hf,deformedPoint_periodic f hf]

theorem signed_weighted_integral_compact_domain (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (w : (Fin N → ℝ) → ℂ) (hw : Continuous w) (hp : CoordinatePeriodic N w)
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    (∫ θ in angleBox N, w θ*signedPulledDensity σ f r τ lam s θ)=
      ∫ θ, compactSignedWeight w θ*signedPulledDensity σ f r τ lam s θ := by
  rw [compactSignedWeight_integral]
  apply angleBox_eq_signed_integral N
  · exact hw.mul (signed_fixedDensity_contDiff σ hσ hN f hf hr hr1 hτ hlam s hs.2).continuous
  · intro θ q
    dsimp only
    rw [hp θ q,signedPulledDensity_periodic σ N f hf r τ lam s θ q]

theorem signed_original_sector_compact_integral_jets (σ : ℂ) (hσ : ‖σ‖ = 1)
    {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (J : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv J (signedOriginalSectorIntegral σ N f r τ b outer inner ho hi (some (q,sigma))) s=
      iteratedDeriv J (fun z => ∫ θ,
        compactSignedWeight (originalSectorAngularWeight f b outer inner ho hi q sigma) θ*
          signedPulledDensity σ f r τ 0 z θ) s := by
  have he : signedOriginalSectorIntegral σ N f r τ b outer inner ho hi (some (q,sigma)) =ᶠ[𝓝 s]
      (fun z => ∫ θ, compactSignedWeight (originalSectorAngularWeight f b outer inner ho hi q sigma) θ*
        signedPulledDensity σ f r τ 0 z θ) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    exact signed_weighted_integral_compact_domain σ hσ N hN f hf hr hr1 hτ le_rfl _
      (originalSectorAngularWeight_regular f hf b outer inner ho hi q sigma).1
      (originalSectorAngularWeight_regular f hf b outer inner ho hi q sigma).2 hz
  exact he.iteratedDeriv_eq J

theorem signed_current_sector_compact_integral_jets (σ : ℂ) (hσ : ‖σ‖ = 1)
    {N : ℕ} (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (qS : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3)
    (J : ℕ) {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv J (signedCurrentSectorIntegral σ N f r τ lam qS b outer inner ho hi (some (q,sigma))) s=
      iteratedDeriv J (fun z => ∫ θ,
        compactSignedWeight (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) θ*
          signedPulledDensity σ f r τ lam z θ) s := by
  have he : signedCurrentSectorIntegral σ N f r τ lam qS b outer inner ho hi (some (q,sigma)) =ᶠ[𝓝 s]
      (fun z => ∫ θ, compactSignedWeight (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) θ*
        signedPulledDensity σ f r τ lam z θ) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    exact signed_weighted_integral_compact_domain σ hσ N hN f hf hr hr1 hτ hlam _
      (currentSectorAngularWeight_regular f hf τ qS b outer inner ho hi q sigma).1
      (currentSectorAngularWeight_regular f hf τ qS b outer inner ho hi q sigma).2 hz
  exact he.iteratedDeriv_eq J

end
end IsingBulk.HT.Tail

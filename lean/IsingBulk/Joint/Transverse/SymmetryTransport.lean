import IsingBulk.Joint.FormFactors.Swap
import IsingBulk.Joint.FormFactors.Conjugation
import IsingBulk.Joint.Final.HolomorphicExtension
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Exact extension transport through physical symmetries
Reflection is applied to both the parameter and the value. No antiholomorphic
curve is incorrectly treated as holomorphic.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter
open scoped Topology

def reflectedCurve (c : ℂ → Coupling) : ℂ → Coupling := fun t => star (c (star t))

theorem reflectedCurve_analyticAt {c : ℂ → Coupling} {z : ℂ} (hc : AnalyticAt ℂ c z) :
    AnalyticAt ℂ (reflectedCurve c) (star z) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hh := hc.eventually_analyticAt
  have ht : Tendsto (star : ℂ→ℂ) (𝓝 (star z)) (𝓝 z) := by
    simpa using (continuous_star.tendsto (star z))
  filter_upwards [ht.eventually hh] with t ht
  convert! ht.differentiableAt.hasDerivAt.star_conj.differentiableAt using 1
  simp only [starRingEnd_apply,star_star]

theorem fullExtension_swapped_curve {D : Set Coupling} {f : Coupling → ℂ}
    (hD : ∀ K, K.swap∈D ↔ K∈D) (hf : ∀ K∈D, f K.swap=f K)
    {c : ℂ→Coupling} {z : ℂ}
    (he : HasFullExtension (c ⁻¹' D) (f∘c) z) :
    HasFullExtension ((fun t => (c t).swap) ⁻¹' D) (fun t => f (c t).swap) z := by
  obtain ⟨U,hU,hz,g,hg,hgf⟩ := he
  refine ⟨U,hU,hz,g,hg,?_⟩
  intro t ht
  have hct := (hD (c t)).mp ht.2
  exact (hgf ⟨ht.1,hct⟩).trans (hf (c t) hct).symm

theorem fullExtension_reflected_curve {D : Set Coupling} {f : Coupling → ℂ}
    (hD : ∀ K, star K∈D ↔ K∈D) (hf : ∀ K∈D, f (star K)=star (f K))
    {c : ℂ→Coupling} {z : ℂ}
    (he : HasFullExtension (c ⁻¹' D) (f∘c) z) :
    HasFullExtension (reflectedCurve c ⁻¹' D) (f∘reflectedCurve c) (star z) := by
  obtain ⟨U,hU,hz,g,hg,hgf⟩ := he
  have hV : IsOpen (star ⁻¹' U) := hU.preimage continuous_star
  refine ⟨star ⁻¹' U,hV,by simpa using hz,fun t => star (g (star t)),?_,?_⟩
  · apply DifferentiableOn.analyticOnNhd _ hV
    intro t ht
    simpa only [Function.comp_def,star_star] using
      (hg (star t) ht).differentiableAt.star_star.differentiableWithinAt (s := star ⁻¹' U)
  · intro t ht
    have hcD : c (star t)∈D := (hD _).mp ht.2
    exact (congrArg star (hgf ⟨ht.1,hcD⟩)).trans (hf _ hcD).symm

theorem holomorphicExtension_swap {D : Set Coupling} {f : Coupling → ℂ}
    (hD : ∀ K, K.swap∈D ↔ K∈D) (hf : ∀ K∈D, f K.swap=f K)
    {K : Coupling} (he : HasHolomorphicFullExtension D f K) :
    HasHolomorphicFullExtension D f K.swap := by
  obtain ⟨U,hU,hK,g,hg,hgf⟩ := he
  refine ⟨Prod.swap ⁻¹' U,hU.preimage continuous_swap,by simpa using hK,g∘Prod.swap,?_,?_⟩
  · intro L hL
    exact (((hg L.swap hL).differentiableAt (hU.mem_nhds hL)).comp L
      (differentiableAt_snd.prodMk differentiableAt_fst)).differentiableWithinAt
  · intro L hL
    exact (hgf ⟨hL.1,(hD L).mpr hL.2⟩).trans (hf L hL.2)

theorem holomorphicExtension_star {D : Set Coupling} {f : Coupling → ℂ}
    (hD : ∀ K, star K∈D ↔ K∈D) (hf : ∀ K∈D, f (star K)=star (f K))
    {K : Coupling} (he : HasHolomorphicFullExtension D f K) :
    HasHolomorphicFullExtension D f (star K) := by
  obtain ⟨U,hU,hK,g,hg,hgf⟩ := he
  refine ⟨star ⁻¹' U,hU.preimage continuous_star,by simpa using hK,
    fun L => star (g (star L)),?_,?_⟩
  · intro L hL
    simpa only [Function.comp_def,star_star] using
      ((hg (star L) hL).differentiableAt (hU.mem_nhds hL)).star_star.differentiableWithinAt
        (s := star ⁻¹' U)
  · intro L hL
    have hh := congrArg star (hgf ⟨hL.1,(hD L).mpr hL.2⟩)
    simpa only [hf L hL.2,star_star] using hh

end
end IsingBulk.Joint.Transverse

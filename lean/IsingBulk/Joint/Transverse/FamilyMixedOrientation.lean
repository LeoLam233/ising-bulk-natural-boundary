import IsingBulk.Joint.Transverse.FamilyOrientationConclusion
import IsingBulk.Joint.Transverse.MixedReflection

/-! All mixed particle-tail transport on a common actual physical tube.
The source majorants are preserved verbatim, including their summability;
no scalar-only derivative estimate is substituted for a mixed derivative. -/
namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric Transverse
open scoped Topology

namespace Transverse

/-- Axis exchange gives equality of the actual full mixed derivative maps. -/
theorem iteratedFDeriv_physical_swapped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set Coupling} {f : Coupling→ℂ} (hD : IsOpen D)
    (hf : ∀K∈D,f K.swap=f K) {curve : E→Coupling} {q : E}
    (hc : ContinuousAt curve q) (hq : curve q∈D) (j : ℕ) :
    iteratedFDeriv ℂ j (fun x=>f (curve x).swap) q=iteratedFDeriv ℂ j (f∘curve) q := by
  have he : (fun x=>f (curve x).swap) =ᶠ[𝓝 q] f∘curve := by
    filter_upwards [hc.preimage_mem_nhds (hD.mem_nhds hq)] with x hx
    exact hf _ hx
  exact (he.iteratedFDeriv ℂ j).eq_of_nhds

set_option maxHeartbeats 400000 in
/-- Reflection preserves the operator norm of the actual mixed derivative,
with all curve-parameter directions included. -/
theorem norm_iteratedFDeriv_physical_reflected {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E]
    {D : Set Coupling} {f : Coupling→ℂ} (hD : IsOpen D)
    (hf : ∀K∈D,f (star K)=star (f K)) {curve : E→Coupling} {q : E} (j : ℕ)
    (hc : ContDiffAt ℂ j curve q) (hq : curve q∈D) (hfa : ContDiffAt ℂ j f (curve q)) :
    ‖iteratedFDeriv ℂ j (fun x=>f (star (curve (star x)))) (star q)‖=
      ‖iteratedFDeriv ℂ j (f∘curve) q‖ := by
  have hs : Tendsto (star : E→E) (𝓝 (star q)) (𝓝 q) := by
    simpa only [star_star] using continuous_star.tendsto (star q)
  have he : (fun x=>f (star (curve (star x)))) =ᶠ[𝓝 (star q)]
      (fun x=>star (f (curve (star x)))) := by
    filter_upwards [hs.eventually (hc.continuousAt.preimage_mem_nhds (hD.mem_nhds hq))] with x hx
    exact hf _ hx
  have hd : ContDiffAt ℂ j (f∘curve) q := hfa.comp q hc
  calc
    _ = ‖iteratedFDeriv ℂ j (fun x=>star (f (curve (star x)))) (star q)‖ :=
      congrArg (fun g : E [×j]→L[ℂ] ℂ => ‖g‖) ((he.iteratedFDeriv ℂ j).eq_of_nhds)
    _ = _ := norm_iteratedFDeriv_star_star (E:=E) (F:=ℂ) (f:=f∘curve) (x:=q) j hd

end Transverse

/-- A summable all-particle majorant for every ambient mixed derivative on
one common tube. The index function includes all parity-dependent tail starts. -/
def CommonMixedParticleMajorants (d : ℕ) (F : ℕ→Coupling→ℂ)
    (curve : ℂ × (Fin d→ℂ)→Coupling) (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ)
    (index : ℕ→ℕ→ℕ) : Prop :=
  ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
    ∀eta∈Q,∀u : ℂ,‖u‖<δ → u∈U → ∀k : ℕ,
      ‖iteratedFDeriv ℂ j (fun q=>F (index j k) (curve q)) (u,eta)‖≤G k

/-- The same all-order envelope on an arbitrary actual approach set. This
includes family-dependent sides such as `Im (B(u,eta)*u)>0`. -/
def CommonMixedParticleMajorantsOn (d : ℕ) (F : ℕ→Coupling→ℂ)
    (curve : ℂ × (Fin d→ℂ)→Coupling) (W : Set (ℂ × (Fin d→ℂ)))
    (index : ℕ→ℕ→ℕ) : Prop :=
  ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
    ∀q∈W,∀k : ℕ,‖iteratedFDeriv ℂ j (fun x=>F (index j k) (curve x)) q‖≤G k

/-- This is a genuine mixed-particle transport interface, separate from the
scalar full-bulk jet interface in `PhysicalFamilyOrientationTransport`. -/
structure MixedPhysicalFamilyOrientationTransport (D : Set Coupling) (F : ℕ→Coupling→ℂ) : Prop where
  mixed_swap : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling) (q : ℂ × (Fin d→ℂ)) (j n : ℕ),
    AnalyticAt ℂ curve q → curve q∈D →
    iteratedFDeriv ℂ j (fun x=>F n (swappedFamily curve x)) q=
      iteratedFDeriv ℂ j (fun x=>F n (curve x)) q
  mixed_reflected : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling) (q : ℂ × (Fin d→ℂ)) (j n : ℕ),
    AnalyticAt ℂ curve q → curve q∈D →
    ‖iteratedFDeriv ℂ j (fun x=>F n (reflectedFamily curve x)) (star q)‖=
      ‖iteratedFDeriv ℂ j (fun x=>F n (curve x)) q‖
  tails_swap_on : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (W : Set (ℂ × (Fin d→ℂ))) (index : ℕ→ℕ→ℕ),
    (∀q∈W,AnalyticAt ℂ curve q ∧ curve q∈D) →
    CommonMixedParticleMajorantsOn d F curve W index →
    CommonMixedParticleMajorantsOn d F (swappedFamily curve) W index
  tails_reflected_on : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (W : Set (ℂ × (Fin d→ℂ))) (index : ℕ→ℕ→ℕ),
    (∀q∈W,AnalyticAt ℂ curve q ∧ curve q∈D) →
    CommonMixedParticleMajorantsOn d F curve W index →
    CommonMixedParticleMajorantsOn d F (reflectedFamily curve) (star ⁻¹' W) index
  tails_swap : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ) (index : ℕ→ℕ→ℕ),
    0<δ → CommonPhysicalFamilyTube D curve Q U δ →
    CommonMixedParticleMajorants d F curve Q U δ index →
    CommonMixedParticleMajorants d F (swappedFamily curve) Q U δ index
  tails_reflected : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ) (index : ℕ→ℕ→ℕ),
    0<δ → CommonPhysicalFamilyTube D curve Q U δ →
    CommonMixedParticleMajorants d F curve Q U δ index →
    CommonMixedParticleMajorants d F (reflectedFamily curve) (star ⁻¹' Q) (star ⁻¹' U) δ index

/-- Only identities and smoothness of the actual particles are used here.
The source summable bounds are conclusions of the substantive oriented engines. -/
theorem mixedPhysicalFamilyOrientationTransport_of_symmetries
    {D : Set Coupling} {F : ℕ→Coupling→ℂ} (hD : IsOpen D)
    (hfs : ∀n K,K∈D → F n K.swap=F n K)
    (hfc : ∀n K,K∈D → F n (star K)=star (F n K))
    (hfd : ∀(j n : ℕ) K,K∈D → ContDiffAt ℂ j (F n) K) :
    MixedPhysicalFamilyOrientationTransport D F where
  mixed_swap := by
    intro d curve q j n hc hq
    exact iteratedFDeriv_physical_swapped hD (hfs n) hc.continuousAt hq j
  mixed_reflected := by
    intro d curve q j n hc hq
    exact norm_iteratedFDeriv_physical_reflected hD (hfc n) j hc.contDiffAt hq (hfd j n _ hq)
  tails_swap_on := by
    intro d curve W index ht hG j
    obtain ⟨G,hGs,hG0,hGb⟩ := hG j
    refine ⟨G,hGs,hG0,?_⟩
    intro q hq k
    obtain ⟨ha,hs⟩ := ht q hq
    change ‖iteratedFDeriv ℂ j (fun x=>F (index j k) (curve x).swap) q‖≤G k
    rw [iteratedFDeriv_physical_swapped hD (hfs _) ha.continuousAt hs j]
    exact hGb q hq k
  tails_reflected_on := by
    intro d curve W index ht hG j
    obtain ⟨G,hGs,hG0,hGb⟩ := hG j
    refine ⟨G,hGs,hG0,?_⟩
    intro q hq k
    obtain ⟨ha,hs⟩ := ht (star q) hq
    have hd := norm_iteratedFDeriv_physical_reflected hD (hfc (index j k)) j
      ha.contDiffAt hs (hfd j (index j k) _ hs)
    change ‖iteratedFDeriv ℂ j (fun x=>F (index j k) (reflectedFamily curve x))
      (star (star q))‖=_ at hd
    rw [star_star] at hd
    rw [hd]
    exact hGb (star q) hq k
  tails_swap := by
    intro d curve Q U δ index _hδ ht hG j
    obtain ⟨G,hGs,hG0,hGb⟩ := hG j
    refine ⟨G,hGs,hG0,?_⟩
    intro eta heta u hu hi k
    obtain ⟨ha,hs⟩ := ht eta heta u hu
    change ‖iteratedFDeriv ℂ j (fun q=>F (index j k) (curve q).swap) (u,eta)‖≤G k
    rw [iteratedFDeriv_physical_swapped hD (hfs _) ha.continuousAt (hs.mpr hi) j]
    exact hGb eta heta u hu hi k
  tails_reflected := by
    intro d curve Q U δ index _hδ ht hG j
    obtain ⟨G,hGs,hG0,hGb⟩ := hG j
    refine ⟨G,hGs,hG0,?_⟩
    intro eta heta u hu hi k
    have hu' : ‖star u‖<δ := by simpa only [norm_star] using hu
    obtain ⟨ha,hs⟩ := ht (star eta) heta (star u) hu'
    have hd := norm_iteratedFDeriv_physical_reflected hD (hfc (index j k)) j
      ha.contDiffAt (hs.mpr hi) (hfd j (index j k) _ (hs.mpr hi))
    change ‖iteratedFDeriv ℂ j (fun x=>F (index j k) (reflectedFamily curve x))
      (star (star u,star eta))‖=_ at hd
    have he : star (star u,star eta)=(u,eta) := by simp only [Prod.star_def,star_star]
    rw [he] at hd
    rw [hd]
    exact hGb (star eta) heta (star u) hu' hi k

end
end IsingBulk.Joint

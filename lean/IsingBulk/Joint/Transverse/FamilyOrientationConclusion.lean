import IsingBulk.Joint.Transverse.FamilyOrientations
import IsingBulk.Joint.Geometry.OrientedRegular

/-! The explicit all-orientation compact-family clause for final assembly.
The source estimates are the already proved oriented estimates. Common domain
sides and radii, analytic families, and the literal physical jets are transported
by proved symmetries; they are not new admissibility assumptions on the target.
-/
namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric Transverse
open scoped Topology

/-- A common tube for a literal physical family, retaining its actual scalar
side rather than merely membership in the spectral complement. -/
def CommonPhysicalFamilyTube {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set Coupling) (curve : ℂ × E→Coupling) (Q : Set E) (U : Set ℂ) (δ : ℝ) : Prop :=
  ∀eta∈Q,∀u : ℂ,‖u‖<δ →
    AnalyticAt ℂ curve (u,eta) ∧ (curve (u,eta)∈D ↔ u∈U)

private theorem commonTube_approach {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set Coupling} {curve : ℂ × E→Coupling} {Q : Set E} {U : Set ℂ} {δ : ℝ}
    (ht : CommonPhysicalFamilyTube D curve Q U δ) {w : ℝ→ℂ}
    (hw : ∀ᶠt : ℝ in 𝓝[>] 0,‖w t‖<δ ∧ w t∈U) :
    ∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,
      ContinuousAt (fun z=>curve (z,eta)) (w t) ∧ curve (w t,eta)∈D := by
  filter_upwards [hw] with t hwt eta heta
  obtain ⟨ha,hs⟩ := ht eta heta (w t) hwt.1
  exact ⟨(ha.comp (f:=fun z : ℂ=>(z,eta)) (analyticAt_id.prod analyticAt_const)).continuousAt,
    hs.mpr hwt.2⟩

/-- The complete symmetry interface for one literal physical susceptibility.
Every finite complex parameter polydisk is covered. The same positive radius
is retained, and arbitrary complex scaling phases are transported exactly. -/
structure PhysicalFamilyOrientationTransport (D : Set Coupling) (f : Coupling→ℂ) : Prop where
  domain_swap : ∀K, K.swap∈D ↔ K∈D
  domain_star : ∀K, star K∈D ↔ K∈D
  tube_swap : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ), 0<δ →
    CommonPhysicalFamilyTube D curve Q U δ →
    CommonPhysicalFamilyTube D (swappedFamily curve) Q U δ
  tube_reflected : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ), 0<δ →
    CommonPhysicalFamilyTube D curve Q U δ →
    CommonPhysicalFamilyTube D (reflectedFamily curve) (star ⁻¹' Q) (star ⁻¹' U) δ
  jet_swap : ∀(c : ℂ→Coupling) (u : ℂ) (j : ℕ), ContinuousAt c u → c u∈D →
    iteratedDeriv j (fun z=>f (c z).swap) u=iteratedDeriv j (f∘c) u
  jet_reflected : ∀(c : ℂ→Coupling) (u : ℂ) (j : ℕ), ContinuousAt c u → c u∈D →
    iteratedDeriv j (f∘reflectedCurve c) (star u)=star (iteratedDeriv j (f∘c) u)
  uniform_swap_approach : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (w r : ℝ→ℂ) (G : (Fin d→ℂ)→ℂ) (j : ℕ),
    (∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,
      ContinuousAt (fun z=>curve (z,eta)) (w t) ∧ curve (w t,eta)∈D) →
    TendstoUniformlyOn (fun t eta=>r t*iteratedDeriv j (fun z=>f (curve (z,eta))) (w t)) G (𝓝[>] 0) Q →
    TendstoUniformlyOn (fun t eta=>r t*iteratedDeriv j (fun z=>f (swappedFamily curve (z,eta))) (w t))
      G (𝓝[>] 0) Q
  uniform_reflected_approach : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (w r : ℝ→ℂ) (G : (Fin d→ℂ)→ℂ) (j : ℕ),
    (∀ᶠt : ℝ in 𝓝[>] 0,∀eta∈Q,
      ContinuousAt (fun z=>curve (z,eta)) (w t) ∧ curve (w t,eta)∈D) →
    TendstoUniformlyOn (fun t eta=>r t*iteratedDeriv j (fun z=>f (curve (z,eta))) (w t)) G (𝓝[>] 0) Q →
    TendstoUniformlyOn (fun t eta=>star (r t)*iteratedDeriv j
      (fun z=>f (reflectedFamily curve (z,eta))) (star (w t)))
      (fun eta=>star (G (star eta))) (𝓝[>] 0) (star ⁻¹' Q)
  uniform_swap : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ) (w r : ℝ→ℂ) (G : (Fin d→ℂ)→ℂ) (j : ℕ),
    0<δ → CommonPhysicalFamilyTube D curve Q U δ →
    (∀ᶠt : ℝ in 𝓝[>] 0,‖w t‖<δ ∧ w t∈U) →
    TendstoUniformlyOn (fun t eta=>r t*iteratedDeriv j (fun z=>f (curve (z,eta))) (w t)) G (𝓝[>] 0) Q →
    TendstoUniformlyOn (fun t eta=>r t*iteratedDeriv j (fun z=>f (swappedFamily curve (z,eta))) (w t))
      G (𝓝[>] 0) Q
  uniform_reflected : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling)
    (Q : Set (Fin d→ℂ)) (U : Set ℂ) (δ : ℝ) (w r : ℝ→ℂ) (G : (Fin d→ℂ)→ℂ) (j : ℕ),
    0<δ → CommonPhysicalFamilyTube D curve Q U δ →
    (∀ᶠt : ℝ in 𝓝[>] 0,‖w t‖<δ ∧ w t∈U) →
    TendstoUniformlyOn (fun t eta=>r t*iteratedDeriv j (fun z=>f (curve (z,eta))) (w t)) G (𝓝[>] 0) Q →
    TendstoUniformlyOn (fun t eta=>star (r t)*iteratedDeriv j
      (fun z=>f (reflectedFamily curve (z,eta))) (star (w t)))
      (fun eta=>star (G (star eta))) (𝓝[>] 0) (star ⁻¹' Q)

private theorem physicalFamilyOrientationTransport_of_symmetries
    {D : Set Coupling} {f : Coupling→ℂ} (hD : IsOpen D)
    (hDs : ∀K, K.swap∈D ↔ K∈D) (hDc : ∀K, star K∈D ↔ K∈D)
    (hfs : ∀K∈D,f K.swap=f K) (hfc : ∀K∈D,f (star K)=star (f K)) :
    PhysicalFamilyOrientationTransport D f where
  domain_swap := hDs
  domain_star := hDc
  tube_swap := by
    intro d curve Q U δ _hδ ht eta heta u hu
    obtain ⟨ha,hs⟩ := ht eta heta u hu
    exact ⟨swappedFamily_analyticAt ha,(hDs _).trans hs⟩
  tube_reflected := by
    intro d curve Q U δ _hδ ht eta heta u hu
    obtain ⟨ha,hs⟩ := ht (star eta) heta (star u) (by simpa only [norm_star] using hu)
    refine ⟨?_,(hDc _).trans hs⟩
    simpa only [Prod.star_def,star_star] using reflectedFamily_analyticAt ha
  jet_swap := fun _ _ j hc hu => iteratedDeriv_swapped_curve hD hfs hc hu j
  jet_reflected := fun _ _ j hc hu => iteratedDeriv_reflected_curve hD hfc hc hu j
  uniform_swap_approach := by
    intro d curve Q w r G j hc h
    exact uniform_scaled_jets_swapped hD hfs j hc h
  uniform_reflected_approach := by
    intro d curve Q w r G j hc h
    exact uniform_scaled_jets_reflected hD hfc j hc h
  uniform_swap := by
    intro d curve Q U δ w r G j _hδ ht hw h
    exact uniform_scaled_jets_swapped hD hfs j (commonTube_approach ht hw) h
  uniform_reflected := by
    intro d curve Q U δ w r G j _hδ ht hw h
    exact uniform_scaled_jets_reflected hD hfc j (commonTube_approach ht hw) h

/-- All regular-prime orientations and all finite complex parameter polydisks,
with literal physical functions and genuine common physical tubes. -/
structure JointFamilyOrientationConclusion : Prop where
  coverage : ∀K, IsPrimeRegularJointEdge K →
    OrientedPrimeJointFace K ∨ OrientedPrimeJointFace (star K) ∨
      OrientedPrimeJointFace K.swap ∨ OrientedPrimeJointFace (star K.swap)
  analytic_swap : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling) (q : ℂ × (Fin d→ℂ)),
    AnalyticAt ℂ curve q → AnalyticAt ℂ (swappedFamily curve) q
  analytic_reflected : ∀(d : ℕ) (curve : ℂ × (Fin d→ℂ)→Coupling) (q : ℂ × (Fin d→ℂ)),
    AnalyticAt ℂ curve q → AnalyticAt ℂ (reflectedFamily curve) (star q)
  compact_parameters : ∀(d : ℕ) (Q : Set (Fin d→ℂ)), IsCompact Q → IsCompact (star ⁻¹' Q)
  disk_radius : ∀(d : ℕ) (eta₀ : Fin d→ℂ) (r : ℝ),
    star ⁻¹' closedBall eta₀ r=closedBall (star eta₀) r
  high_frontier : ∀K, K∈frontier highDomain →
    K.swap∈frontier highDomain ∧ star K∈frontier highDomain
  low_frontier : ∀K, K∈frontier lowDomain →
    K.swap∈frontier lowDomain ∧ star K∈frontier lowDomain
  high : PhysicalFamilyOrientationTransport highDomain FormFactors.highNormalizedBulk
  low : PhysicalFamilyOrientationTransport lowDomain FormFactors.lowNormalizedBulk

/-- This theorem is intended as a USED field of the final J AND R AND I
conjunction, alongside the substantive oriented compact-family estimates. -/
theorem joint_family_orientation_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) : JointFamilyOrientationConclusion where
  coverage := fun _ hK => primeRegular_oriented_cases hK
  analytic_swap := fun _ _ _ hc => swappedFamily_analyticAt hc
  analytic_reflected := fun _ _ _ hc => reflectedFamily_analyticAt hc
  compact_parameters := fun _ _ hQ => isCompact_reflected_parameters hQ
  disk_radius := fun _ eta₀ r => reflected_closedBall eta₀ r
  high_frontier := fun K hK => ⟨(swap_frontier_high_iff K).mpr hK,(star_frontier_high_iff K).mpr hK⟩
  low_frontier := fun K hK => ⟨(swap_frontier_low_iff K).mpr hK,(star_frontier_low_iff K).mpr hK⟩
  high := physicalFamilyOrientationTransport_of_symmetries highDomain_isOpen
    swap_highDomain_iff star_highDomain_iff
    (fun _ hK=>FormFactors.highNormalizedBulk_swap hK)
    (fun _ hK=>FormFactors.highNormalizedBulk_conjugate hphys hK)
  low := physicalFamilyOrientationTransport_of_symmetries lowDomain_isOpen
    swap_lowDomain_iff star_lowDomain_iff
    (fun _ hK=>FormFactors.lowNormalizedBulk_swap hK)
    (fun _ hK=>FormFactors.lowNormalizedBulk_conjugate hphys hK)

end
end IsingBulk.Joint

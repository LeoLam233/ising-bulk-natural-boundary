import IsingBulk.AnisoF002.C03.RegularIsotropicAnchoredDensity

/-!
# The actual anchored current is smooth on the entire compact cycle

No total-coincidence exceptional set is needed. Outside the literal
cutoff support every full descendant and flux has its exact zero germ.
Inside, the independently constructed one-sided inverse and the genuine
physical root prove smoothness and parameter holomorphy at every order.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Filter Metric
open IsingBulk.AnisoF002.RegularTail

structure AnchoredCurrentState {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) : Prop where
  smooth : ContDiffAt ℝ ∞ (anchoredTransportedDensity a σ η τ ξ g j) q
  analytic : AnalyticAt ℂ (fun s => anchoredTransportedDensity a σ η τ ξ g j (s, q.2)) q.1
  flux : ∀ i, DifferentiableAt ℝ (anchoredTransportedFlux a σ η τ ξ g j i) q
  current : ∀ anchor : Fin N,
    scalarPartial (anchoredTransportedDensity a σ η τ ξ g j) actualTimeDirection q -
      (∑ i ∈ Finset.univ.erase anchor,
        scalarPartial (anchoredTransportedFlux a σ η τ ξ g j i)
          (actualAngularDirection i - actualAngularDirection anchor) q) =
      anchoredTransportedDensity a σ η τ ξ g (j + 1) q

theorem anchoredCurrentState_outside {N : ℕ} (a : Fin N) (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (j : ℕ) (q : ℂ × (Fin N → ℝ)) (hq : q.2 ∉ tsupport g) :
    AnchoredCurrentState a σ η τ ξ g j q := by
  have hz := anchoredTransportedDensity_zero_germ a σ η τ ξ g j q hq
  have hn := anchoredTransportedDensity_zero_germ a σ η τ ξ g (j + 1) q hq
  have hf (i : Fin N) := anchoredTransportedFlux_zero_germ a σ η τ ξ g j i q hq
  refine ⟨contDiffAt_const.congr_of_eventuallyEq hz, ?_, ?_, ?_⟩
  · have hm : ContinuousAt (fun s : ℂ => (s, q.2)) q.1 := continuousAt_id.prodMk continuousAt_const
    have he : (fun s => anchoredTransportedDensity a σ η τ ξ g j (s, q.2))
        =ᶠ[𝓝 q.1] (fun _ => 0) := hm.eventually hz
    exact analyticAt_const.congr he.symm
  · intro i
    exact (contDiffAt_const.congr_of_eventuallyEq (hf i) :
      ContDiffAt ℝ ∞ (anchoredTransportedFlux a σ η τ ξ g j i) q).differentiableAt (by simp)
  · intro anchor
    unfold scalarPartial
    rw [hz.fderiv_eq, fderiv_const_apply, zero_apply, hn.eq_of_nhds]
    simp only [(hf _).fderiv_eq, fderiv_const_apply, zero_apply, Finset.sum_const_zero, sub_zero]

theorem exists_actual_anchored_current_buffer (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ N : ℕ, 0 < N → ∀ a : Fin N, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
      ∀ g : (Fin N → ℝ) → ℂ, ContDiff ℝ ∞ g →
      (∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc (-Real.pi - β) β) →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ s : ℂ, 0 < s.im → dist s (S : ℂ) < δ → ∀ θ : Fin N → ℝ,
      ∀ j : ℕ, AnchoredCurrentState a σ η τ ξ g j (s, θ) := by
  obtain ⟨βF, hβF, hβF1, hframes⟩ := exists_actual_anchored_frame_buffer S hS
  obtain ⟨rG, κ, A, M, hrG, _, _, _, hgauss⟩ :=
    exists_actual_oneSided_retainedNumerator_analytic_gaussian S hS
  obtain ⟨δI, hδI, himage⟩ := exists_actual_oneSided_homotopy_domain S rG hS hrG
  let β := min βF (δI / 2)
  have hβ : 0 < β := lt_min hβF (half_pos hδI)
  have hbF : β ≤ βF := min_le_left _ _
  have hbI : β < δI := (min_le_right _ _).trans_lt (half_lt_self hδI)
  have hβ1 : β ≤ 1 := hbF.trans hβF1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη
  obtain ⟨δF, hδF, _, hjets, hframe⟩ := hframes η hη
  let δ := min β δF
  have hδ : 0 < δ := lt_min hβ hδF
  have hdβ : δ ≤ β := min_le_left _ _
  have hdF : δ ≤ δF := min_le_right _ _
  have hdI : δ < δI := hdβ.trans_lt hbI
  refine ⟨δ, hδ, hdβ, ?_⟩
  intro N hN a σ hσ g hg hsupp τ ξ hτ hξ s hs hsnear θ j
  by_cases hsupport : θ ∈ tsupport g
  · have hθ := hsupp θ hsupport
    obtain ⟨hp, hUeq⟩ := himage N hN s hs (hsnear.trans hdI) η τ ξ hη
      ⟨hτ.1, hτ.2.trans hdI.le⟩ hξ θ
      (fun i => ⟨by linarith only [(hθ i).1, hbI], (hθ i).2.trans hbI.le⟩)
    obtain ⟨hχ, hdet, hU, hB, hK, hV⟩ := hframe N hN s hs (hsnear.trans_le hdF) τ ξ
      ⟨hτ.1, hτ.2.trans hdF⟩ hξ θ
      (fun i => ⟨by linarith only [(hθ i).1, hbF], (hθ i).2.trans hbF⟩) a
    let p : RegularJointSpace N := regularJointMap (actualPhysicalCoordinate η τ ξ) (s, θ)
    have hUp (i : Fin N) : AnalyticAt ℂ explicitRightInverse (p.1, p.2 i) := hU i
    have hR (i : Fin N) : ‖regularInverseRoot (p.1, p.2 i)‖ < 1 := by
      change ‖regularInverseRoot ((s, θ).1, actualPhysicalCoordinate η τ ξ i (s, θ))‖ < 1
      rw [regularInverseRoot_actual η τ ξ (s, θ) i (hUeq i)]
      exact upperEdgeRoot_norm_lt_one
        (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i)
    have hprod : ‖regularRootProduct p‖ ≤ ‖regularInverseRoot (p.1, p.2 a)‖ :=
      product_norm_le_named_factor _ (fun i => (hR i).le) a
    have hmid : ‖regularRootProduct p‖ ≤ (1 + ‖regularInverseRoot (p.1, p.2 a)‖) / 2 := by
      linarith only [hprod, hR a]
    have hker := (regularProductKernel_control σ hσ p ‖regularInverseRoot (p.1, p.2 a)‖
      (norm_nonneg _) (hR a) hmid hUp).1
    have hnum := (hgauss N ∅ (Finset.empty_subset _) p hp).1
    rw [retainedRegularNumerator_empty] at hnum
    have hF : AnalyticAt ℂ (anchoredRegularDensity σ) p :=
      (analyticAt_const.mul hker).mul hnum
    have hAsmooth (i l : Fin N) : ContDiff ℝ ∞ (actualBalancedInverseEntry η τ ξ i l) := by
      apply contDiff_infty.mpr
      intro k
      obtain ⟨Ck, _, hk⟩ := hjets k
      exact (hk N hN τ ξ ⟨hτ.1, hτ.2.trans hdF⟩ hξ i l).smooth
    obtain ⟨hsm, hflux, hcurrent⟩ := anchoredTransportedDensity_current a σ η τ ξ g j (s, θ)
      hχ hdet hB hF hg.contDiffAt (hV.mono (fun _ hy => hy.1))
    refine ⟨hsm, ?_, hflux, hcurrent⟩
    have hpar := coordinateTransportDescendant_parameter_analyticAt (anchoredRegularField a)
      (anchoredCutoffCoefficient a) η τ ξ (anchoredRegularDensity σ) g hAsmooth hg θ s
      hη hτ.1 hξ.1 hs (fun i => (hχ i).of_le (by simp)) hB hK hF hdet
      (hV.mono (fun _ hy => hy.2)) j
    exact (actualCoordinateDeterminant_parameter_analyticAt η τ ξ θ s hη hτ.1 hξ.1 hs).mul hpar
  · exact anchoredCurrentState_outside a σ η τ ξ g j (s, θ) hsupport

end IsingBulk.AnisoF002.Isotropic

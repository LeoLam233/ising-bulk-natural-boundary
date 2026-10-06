import IsingBulk.First.OnsiteAuxiliaryJets
import IsingBulk.First.OnsiteRadialRegularChart

/-! The bounded auxiliary region is controlled by an actual compact source
coefficient family, separately from the large-radius integration by parts. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff dispersionAuxiliaryTotal_contDiff

theorem onsiteAuxiliaryJet_eq_zero {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (u : DoubleAngularVector N) (hw : w u = 0) :
    onsiteAuxiliaryJet r s w J j ξ u = 0 := by
  have he : (fun z => onsiteRegularAmplitude r z w J u *
      Complex.exp (sourcePhaseSum r z (fun _ => 1) (fun _ => 1) (fun f : J => f.1) ξ u)) =
      fun _ => 0 := by funext z; simp [onsiteRegularAmplitude,hw]
  unfold onsiteAuxiliaryJet
  rw [he, ← iteratedDeriv_eq_iterate]
  simp

theorem onsiteAuxiliaryJet_norm_le_normalized {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (j : ℕ) (ξ : J → ℝ) (hξ : ∀ f, 0 ≤ ξ f) (u : DoubleAngularVector N)
    (hdom : ((r,s),u) ∈ onsiteInactiveDomain J) (hr : 0 < r) (hr1 : r ≤ 1)
    (hm : r⁻¹-r ≤ (sourceS s).im) :
    ‖onsiteAuxiliaryJet r s w J j ξ u‖ ≤
      ‖onsiteNormalizedAmplitude 1 (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ) r s w J j u‖ := by
  rw [onsiteAuxiliaryJet_normalize r s w J j ξ 1 one_ne_zero u hdom.2.1 hdom.2.2]
  simp only [Complex.ofReal_one, one_pow, one_mul, div_one, inv_one, onsiteIBPAmplitude,
    sourceIBPPhase, norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  exact sourcePhaseSum_re_nonpositive_closed hr hr1 hm _ _ (by simp) (by simp) _ _ hξ u

/-- Every fixed parameter derivative of the literal exponential inner angular
integral is uniformly bounded on the actual bounded auxiliary cube. -/
theorem onsite_radial_small_auxiliary_bound {N : ℕ} (θ S : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) = (S : ℂ))
    (u₀ : DoubleAngularVector N) (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f, f ∈ J ↔ isOnsiteFactor f ∧ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2) S f) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ w : DoubleAngularVector N → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc 0 ε₀, ∀ ξ ∈ Icc (0 : J → ℝ) 1,
        ‖∫ u, onsiteAuxiliaryJet (sourceRadialPair θ ε).1 (sourceRadialPair θ ε).2 w J j ξ u‖ ≤ C := by
  obtain ⟨γ,ε₀,hγ,he₀,hphys,hdom⟩ := onsite_radial_regular_chart θ S hθ hS u₀ J hJ
  refine ⟨γ,ε₀,hγ,he₀,?_⟩
  intro w hw hsupp j
  let K : Set (ℝ × (J → ℝ)) := Icc 0 ε₀ ×ˢ Icc 0 1
  let L : Set (DoubleAngularVector N) := Metric.closedBall u₀ γ
  let B : (ℝ × (J → ℝ)) → DoubleAngularVector N → ℂ := fun z u =>
    onsiteNormalizedAmplitude 1 (dispersionAuxiliaryTotal (fun f : J => f.1) z.2 : ℂ)
      (sourceRadialPair θ z.1).1 (sourceRadialPair θ z.1).2 w J j u
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hL : IsCompact L := isCompact_closedBall u₀ γ
  have hc : HasCompactSupport w := hL.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hB : ContinuousOn (fun z : (ℝ × (J → ℝ)) × DoubleAngularVector N => B z.1 z.2) (K ×ˢ L) := by
    rintro ⟨⟨ε,ξ⟩,u⟩ ⟨⟨hε,hξ⟩,hu⟩
    have h := onsiteNormalizedAmplitude_joint_contDiffAt w hw J 1
      (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ)
      (sourceRadialPair θ ε).1 (sourceRadialPair θ ε).2 u (hdom ε hε u hu) j
    let F : (ℝ × (J → ℝ)) × DoubleAngularVector N → SourceNormalizedParameter N × ℂ :=
      fun z => (((1,(dispersionAuxiliaryTotal (fun f : J => f.1) z.1.2 : ℂ)),
        ((sourceRadialPair θ z.1.1).1,z.2)),(sourceRadialPair θ z.1.1).2)
    have hF : ContDiff ℝ ∞ F := by
      unfold F sourceRadialPair IsingBulk.Branch.radialParameter
      fun_prop
    exact (h.comp ((ε,ξ),u) (f := F) hF.contDiffAt).continuousAt.continuousWithinAt
  have hzero (z : ℝ × (J → ℝ)) (_hz : z ∈ K) (u : DoubleAngularVector N) (hu : u ∉ L) : B z u = 0 := by
    apply onsiteNormalizedAmplitude_eq_zero
    by_contra hwu
    exact hu (hsupp (subset_closure hwu))
  let : (volume : Measure (DoubleAngularVector N)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin N → ℝ)) (volume : Measure (Fin N → ℝ))
  obtain ⟨C,hC,hmass⟩ := uniform_compact_integral_norm_bound (μ := volume) hK hL B hB hzero
  refine ⟨C,hC,?_⟩
  intro ε hε ξ hξ
  have hpar := hphys ε hε
  have hden : ∀ u ∈ tsupport w, ∀ f ∈ Jᶜ,
      onsiteFactorDenominator (sourceRadialPair θ ε).2
        (angleTuple (sourceRadialPair θ ε).1 u.1) (angleTuple (sourceRadialPair θ ε).1 u.2) f ≠ 0 :=
    fun u hu => (hdom ε hε u (hsupp hu)).2.2
  have hcont := onsiteNormalizedAmplitude_contDiff 1
    (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ)
    (sourceRadialPair θ ε).1 (sourceRadialPair θ ε).2 w hw J hpar.1.ne' hpar.2.2.1 hden j
  have hcomp := onsiteNormalizedAmplitude_hasCompactSupport 1
    (dispersionAuxiliaryTotal (fun f : J => f.1) ξ : ℂ)
    (sourceRadialPair θ ε).1 (sourceRadialPair θ ε).2 w hc J j
  have hBI : Integrable (fun u => ‖B (ε,ξ) u‖) :=
    (hcont.continuous.integrable_of_hasCompactSupport hcomp).norm
  calc
    _ ≤ ∫ u, ‖B (ε,ξ) u‖ := by
      apply norm_integral_le_of_norm_le hBI
      exact Eventually.of_forall (fun u => by
        by_cases hu : u ∈ L
        · exact onsiteAuxiliaryJet_norm_le_normalized _ _ w J j ξ hξ.1 u
            (hdom ε hε u hu) hpar.1 hpar.2.1 hpar.2.2.2
        · have hw0 : w u = 0 := by
            by_contra hwu
            exact hu (hsupp (subset_closure hwu))
          rw [onsiteAuxiliaryJet_eq_zero _ _ w J j ξ u hw0, norm_zero]
          exact norm_nonneg _)
    _ ≤ C := hmass (ε,ξ) ⟨hε,hξ⟩

end
end IsingBulk.First

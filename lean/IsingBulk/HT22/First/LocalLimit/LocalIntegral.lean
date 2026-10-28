import IsingBulk.HT22.First.LocalLimit.AngularBridge
import IsingBulk.First.RegularPostMeanIntegral
import IsingBulk.First.ActualLeadingCoordinateLimit

/-! The actual normalized dependent-angle local integral, its reflected chart,
and the local derivative identity. No asymptotic is an assumption. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set MeasureTheory Filter Metric IsingBulk.First IsingBulk.Tail
open scoped BigOperators Topology

def angularLocalIntegral {n : ℕ} (α : ℝ) (χ : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ u : Fin n → ℝ, χ (shapeCoordinateEquiv n (WithLp.toLp 2 u)) *
    ((((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹ *
      Physical.signedAngularDensity false s
        (Physical.constrainedAngles false n (fun i => u i-α)))

def angularUpperLocalIntegral {n : ℕ} (α : ℝ) (χ : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ u : Fin n → ℝ, χ (shapeCoordinateEquiv n (WithLp.toLp 2 u)) *
    ((((n+1).factorial:ℂ)*(2*(Real.pi:ℂ))^n)⁻¹ *
      Physical.signedAngularDensity false s
        (Physical.constrainedAngles false n (fun i => α-u i)))

theorem angularUpperLocalIntegral_eq_lower {n : ℕ} (α : ℝ)
    (χ : ShapeSpace n → ℂ) (s : ℂ) :
    angularUpperLocalIntegral α χ s=angularLocalIntegral α χ s := by
  unfold angularUpperLocalIntegral angularLocalIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    have h := Physical.constrainedDensity_reflect false n s (fun i => u i-α)
    have he : (fun i => α-u i)=(fun i => -(u i-α)) := by funext i;ring
    rw [he,h]

/-- The radius is proved from the genuine local source domain. In particular,
all angular pair gaps, including repeated indices, are discharged uniformly. -/
theorem lowerChart_pair_gap_radius (a : RegularChartData) (n : ℕ) :
    ∃ R : ℝ, 0<R ∧ ∀ x : ShapeSpace n, ‖x‖<R →
      ∀ i j : Fin (n+1),
        1-shapeY a.alpha (intrinsicShapeCoordinates x) i*
          shapeY a.alpha (intrinsicShapeCoordinates x) j≠0 := by
  let z := exp ((a.theta:ℂ)*I)
  have hmap : Continuous (fun x : ShapeSpace n => (z,intrinsicShapeCoordinates x)) :=
    continuous_const.prodMk (intrinsicShapeCoordinates_continuous n)
  have ht : Tendsto (fun x : ShapeSpace n => (z,intrinsicShapeCoordinates x))
      (𝓝 0) (𝓝 (z,0)) := by
    have hzero : intrinsicShapeCoordinates (0:ShapeSpace n)=(0:Fin n → ℝ) := rfl
    simpa only [hzero] using hmap.tendsto (0:ShapeSpace n)
  have hevent := ht.eventually (IsingBulk.First.Regular.actualDensityDomain_eventually a n)
  obtain ⟨R,hR,hB⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨R,hR,?_⟩
  intro x hx
  exact (hB (mem_ball_zero_iff.mpr hx)).2.2.1

/-- Exact source identity on the physical exterior upper domain, for a fixed
cutoff supported in the proved regular chart. -/
theorem angularLocalIntegral_eq_postMean {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      (∀ x,χ x≠0 → ‖x‖<R) → ∀ s : ℂ, 1<‖s‖ → 0<(sourceS s).im →
      angularLocalIntegral a.alpha χ s=
        IsingBulk.First.Regular.localizedPostMeanIntegral a χ s := by
  obtain ⟨R,hR,hgap⟩ := lowerChart_pair_gap_radius a n
  refine ⟨R,hR,?_⟩
  intro χ hχ s hs hi
  unfold angularLocalIntegral IsingBulk.First.Regular.localizedPostMeanIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    by_cases hz : χ (shapeCoordinateEquiv n (WithLp.toLp 2 u))=0
    · simp only [hz,zero_mul]
    · have hgu := hgap _ (hχ _ hz)
      rw [intrinsicShapeCoordinates_shapeCoordinateEquiv] at hgu
      rw [constrainedDensity_lowerChart s a.alpha u ha,
        postMeanDensity_eq_angular hs hi a.alpha u ha hgu]
      simp only [mul_inv_rev,div_eq_mul_inv]
      ring

/-- All complex parameter derivatives agree on that same actual exterior
neighborhood; real shape cutoffs remain fixed during differentiation. -/
theorem angularLocalIntegral_deriv_eq_postMean {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1) :
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      (∀ x,χ x≠0 → ‖x‖<R) → ∀ s : ℂ, 1<‖s‖ → 0<(sourceS s).im → ∀ k : ℕ,
      (deriv^[k] (angularLocalIntegral a.alpha χ)) s=
        (deriv^[k] (IsingBulk.First.Regular.localizedPostMeanIntegral a χ)) s := by
  obtain ⟨R,hR,hEq⟩ := angularLocalIntegral_eq_postMean a ha
  refine ⟨R,hR,?_⟩
  intro χ hχ s hs hi k
  have hs0 : s≠0 := norm_ne_zero_iff.mp (by linarith)
  have hSc : ContinuousAt sourceS s := continuousAt_id.add (continuousAt_id.inv₀ hs0)
  have hnorm : ∀ᶠ z : ℂ in 𝓝 s,1<‖z‖ :=
    continuous_norm.continuousAt.eventually (Ioi_mem_nhds hs)
  have hupper : ∀ᶠ z : ℂ in 𝓝 s,0<(sourceS z).im :=
    (continuous_im.continuousAt.comp hSc).eventually (Ioi_mem_nhds hi)
  have heq : angularLocalIntegral a.alpha χ =ᶠ[𝓝 s]
      IsingBulk.First.Regular.localizedPostMeanIntegral a χ := by
    filter_upwards [hnorm,hupper] with z hz hu
    exact hEq χ hχ z hz hu
  simpa only [iteratedDeriv_eq_iterate] using heq.iteratedDeriv_eq k

end
end IsingBulk.HT22.LocalLimit

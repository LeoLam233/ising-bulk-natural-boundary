import IsingBulk.HT22.Geometry.LocalizedSignedContour
import IsingBulk.HT22.Geometry.LocalizedSignedBounds
import IsingBulk.HT22.Geometry.SignedCriticalPlateau
import IsingBulk.HT22.Physical.Symmetries

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.Preferred22 IsingBulk.First LocalLimit
open scoped Topology BigOperators

def rightContourWeight {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight .right η p m r θ:ℂ)*(preferredContourMatrix τ p m θ).det /
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

theorem rightContourWeight_density {N : ℕ} (negative : Bool) (τ : ℝ)
    (η p m r : ℝ → ℝ) (θ : Fin N → ℝ) (t : ℂ) :
    rightContourWeight τ η p m r θ*Physical.complexSignedDensity negative (t,deformedAngles τ p m θ)=
      (preferredCellWeight .right η p m r θ:ℂ)*Physical.bareContourDensity negative τ p m t θ := by
  unfold rightContourWeight Physical.bareContourDensity
  simp only [div_eq_mul_inv]
  ring

theorem signedAngularDensity_lift {N : ℕ} (negative : Bool) (δ : ℝ) (θ : Fin N → ℝ) (t : ℂ) :
    Physical.signedAngularDensity negative t (preferredLiftedAngles δ θ)=
      Physical.signedAngularDensity negative t θ := by
  apply Physical.signedAngularDensity_congr_angles
  intro i
  exact preferred_periodic_lift angleRoot angleRoot_periodic δ (θ i)

/-- Exact critical source localization, including the original population
and right weights, full contour Jacobian, factorial, Haar normalization,
and signed dependent angle. The target is the actual physical local
integral, not a model or a leading-order approximation. -/
theorem signed_critical_localized_integral (n : ℕ) (negative : Bool)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (δB : ℝ) (rcut : ℝ → ℝ)
    (hrcut : PreferredRightCutoffData d B δB rcut) (l : ℤ)
    (hcrit : signedEqualityMean negative (n+1) l= -d.alpha) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin n → ℝ) → ℂ,
      (∀ θ,χ θ≠0 → ‖θ-(fun _ => -d.alpha)‖<R) → ∀ τ : ℝ,∀ t : ℂ,
      localizedSignedLiftedIntegral n negative d B τ χ
        (rightContourWeight τ preferredPopulationCutoff B.p B.m rcut) t =
      ∫ u : Fin n → ℝ,χ (fun i => u i-d.alpha)*
        (Physical.signedAngularDensity negative t
          (Physical.constrainedAngles negative n (fun i => u i-d.alpha)) /
          (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n)) := by
  obtain ⟨ρ,hρ,hseed⟩ := signed_first_chart_seed_neighborhood d B δB rcut hrcut
  have hgap : 0<d.b-d.alpha := sub_pos.mpr (preferred_alpha_lt_branch d)
  have hmean : signedEqualityMean negative (n+1) l∈Icc (-d.b+(d.b-d.alpha)) B.delta := by
    rw [hcrit]
    constructor <;> linarith [B.delta_pos,d.alpha_pos]
  obtain ⟨Ra,hRa,hchart⟩ := regular_signed_mean_chart_radius n negative d B l hgap hmean
  let c := Physical.constraintAngle negative+2*Real.pi*(l:ℝ)
  let θ₀ : Fin n → ℝ := fun _ => -d.alpha
  have hc : c/((n+1:ℕ):ℝ)= -d.alpha := by
    simpa only [c,signedEqualityMean,add_comm] using hcrit
  have hcenter : constrainedAtTotal c θ₀=(fun _ => -d.alpha) := by
    have hz : shapeExtend (0:Fin n → ℝ)=0 := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [shapeExtend]
    simpa only [hc,hz,Pi.zero_apply,add_zero] using constrainedAtTotal_translate_mean n c (0:Fin n → ℝ)
  have hev : ∀ᶠ θ in 𝓝 θ₀,∀ i,|constrainedAtTotal c θ i+d.alpha|<ρ := by
    apply eventually_all.mpr
    intro i
    have hcont : Continuous (fun θ : Fin n → ℝ => |constrainedAtTotal c θ i+d.alpha|) := by
      unfold constrainedAtTotal
      fun_prop
    exact hcont.continuousAt.eventually (Iio_mem_nhds (by simp only [hcenter,neg_add_cancel,abs_zero]; exact hρ))
  obtain ⟨Rb,hRb,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min Ra Rb,lt_min hRa hRb,?_⟩
  intro χ hsupp τ t
  let F : (Fin n → ℝ) → ℂ := fun θ => χ θ*
    (Physical.signedAngularDensity negative t (Physical.constrainedAngles negative n θ) /
      (((n+1).factorial:ℂ)*(2*Real.pi:ℂ)^n))
  have hpt (θ : Fin n → ℝ) :
      (let w := preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)
       χ θ*rightContourWeight τ preferredPopulationCutoff B.p B.m rcut w*
        Physical.complexSignedDensity negative (t,deformedAngles τ B.p B.m w))=F θ := by
    by_cases hz : χ θ=0
    · simp only [hz,zero_mul,F]
    · have hθ := hsupp θ hz
      have ha := hchart θ (by simpa only [hcrit] using hθ.trans_le (min_le_left _ _))
      have hb := hball (show θ∈ball θ₀ Rb by
        simpa only [mem_ball,dist_eq_norm] using hθ.trans_le (min_le_right _ _))
      dsimp only
      rw [mul_assoc,rightContourWeight_density]
      have hnear (i : Fin (n+1)) : |preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ) i+d.alpha|<ρ := by
        rw [ha.2]
        exact hb i
      rw [hseed (n+1) (by omega) _ hnear negative τ t,signedAngularDensity_lift]
      rfl
  have hzero (θ : Fin n → ℝ) (hθ : θ∉angularBox n) : F θ=0 := by
    have hz : χ θ=0 := by
      by_contra hh
      have ha := hchart θ (by simpa only [hcrit] using (hsupp θ hh).trans_le (min_le_left _ _))
      exact hθ ha.1
    simp only [F,hz,zero_mul]
  unfold localizedSignedLiftedIntegral
  rw [show (fun θ => let w := preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)
      χ θ*rightContourWeight τ preferredPopulationCutoff B.p B.m rcut w*
        Physical.complexSignedDensity negative (t,deformedAngles τ B.p B.m w))=F from funext hpt]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,←integral_add_right_eq_self F (fun _ => -d.alpha)]
  rfl

end
end IsingBulk.HT22.Geometry

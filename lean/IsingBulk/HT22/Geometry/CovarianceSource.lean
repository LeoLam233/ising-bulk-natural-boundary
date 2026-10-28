import IsingBulk.HT22.Geometry.ActualSlopeScale
import IsingBulk.HT22.Transport.CovarianceSecants
import IsingBulk.HT22.Transport.SourceField

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology BigOperators
open Set IsingBulk.Preferred22

def actualRegularCoordinates {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  fun i => sumCoordinate (IsingBulk.Branch.radialParameter d.alpha ε) (deformedAngles τ B.p B.m θ i)

/-- F001's literal mixed covariance has the required projected lower bound
on every actual fixed-occupancy right contour. The interval [a,b] is any
interval containing its angles and lying in the declared right shell;
it introduces neither a changing particle cutoff nor a phase hypothesis. -/
theorem actual_mixed_covariance_lower (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c ε₀ τ₀ δB : ℝ, 0<c ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r a b : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → -d.b-δB≤a → b≤B.delta →
      μ-2*r≤a+d.b → b+d.b≤μ+2*r → ∀ θ : Fin N → ℝ,
      (∀ i, θ i∈Icc a b) →
      (c/Real.sqrt (|μ|+r+ε))*((∑ i,∑ j,(θ i-θ j)^2)/2) ≤
        (covarianceDirection*sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε)
          (actualRegularCoordinates d B ε τ θ)).re := by
  obtain ⟨c,e,t,δ,hc,he,ht,hδ,hδB,hslope⟩ := actual_inverse_slope_scale d B
  obtain ⟨K,hK,hsec⟩ := actual_bump_secant_error d B
  obtain ⟨em,hem,hmarg⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (by linarith [B.delta_alpha,d.alpha_pos])
  let τ₀ := min t (1/(20*K))
  have hτ₀ : 0<τ₀ := lt_min ht (by positivity)
  refine ⟨c/10,min e em,τ₀,δ,by positivity,lt_min he hem,hτ₀,hδ,hδB,?_⟩
  intro N hN ε τ μ r a b hε hεr hτ hτr hr ha hb hwa hwb θ hθ
  have hbox (x : ℝ) (hx : x∈Icc a b) : x∈Icc (-d.b-δ) B.delta :=
    ⟨ha.trans hx.1,hx.2.trans hb⟩
  have hwin (x : ℝ) (hx : x∈Icc a b) : μ-2*r≤x+d.b ∧ x+d.b≤μ+2*r := by
    constructor <;> linarith [hx.1,hx.2]
  have hprincipal (x : ℝ) (hx : x∈Icc a b) : x∈Icc (-Real.pi) Real.pi := by
    have hh := hbox x hx
    constructor <;> linarith [hh.1,hh.2,B.branch_plateau,hδB,B.delta_alpha,d.alpha_lt,Real.pi_pos]
  let σ := occupancy B.p θ/(N:ℝ)
  let υ := occupancy B.m θ/(N:ℝ)
  let f := occupancyInverseV d B.m B.p ε τ σ υ
  let w := preferredBumpAngle B.m B.p τ σ υ
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  obtain ⟨hder,hcont,hbounds⟩ := hslope N hN ε τ μ r hε
    (hεr.trans_le (min_le_left _ _)) hτ (hτr.trans_le (min_le_left _ _)) hr θ
    (fun i => hbox _ (hθ i)) (fun i => hwin _ (hθ i))
  have hdist : 2*K*τ≤(1/10:ℝ) := by
    have hlim := hτr.trans_le (min_le_right t (1/(20*K)))
    have hh := (lt_div_iff₀ (by positivity : 0<20*K)).mp hlim
    nlinarith
  have hR := mixedCovariance_secant_bound θ f (deriv f) w covarianceDirection a b
    (1/5) (1/10) (c/Real.sqrt (|μ|+r+ε)) hθ (by norm_num) (by norm_num)
    (by rw [covarianceDirection_norm])
    (fun x hx => hder x (hbox x hx)) (hcont.mono (fun _ hx => hbox _ hx))
    (fun x hx => (hbounds x (hbox x hx) (hwin x hx).1 (hwin x hx).2).1)
    (fun x hx => (hbounds x (hbox x hx) (hwin x hx).1 (hwin x hx).2).2)
    (fun x hx y hy hxy => (hsec τ σ υ x y hτ hσ hυ (hprincipal x hx) (hprincipal y hy) hxy).trans
      (mul_le_mul_of_nonneg_right hdist (sub_nonneg.mpr hxy)))
  obtain ⟨hS,_,hSδ⟩ := hmarg ε hε (hεr.trans_le (min_le_right _ _))
  have hU (i : Fin N) : regularInverse (IsingBulk.Branch.radialParameter d.alpha ε)
      (actualRegularCoordinates d B ε τ θ i)=w (θ i) := by
    unfold actualRegularCoordinates
    rw [actual_bump_angle d B τ θ i]
    apply global_one_sided_inverse _ _ B.delta B.delta_pos
      (by linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]) hS hSδ
    · simpa [preferredBumpAngle] using
        (show -Real.pi-B.delta≤θ i by have := (hprincipal _ (hθ i)).1; linarith [B.delta_pos])
    · simpa [preferredBumpAngle] using (hbox _ (hθ i)).2
    · exact preferredBumpW_im_pos d B hε hτ hσ.1 hυ.1 (θ i)
  have hv (i : Fin N) : inverseV (IsingBulk.Branch.radialParameter d.alpha ε)
      (actualRegularCoordinates d B ε τ θ i)=f (θ i) := by
    dsimp [actualRegularCoordinates,f,occupancyInverseV]
    rw [actual_bump_angle d B τ θ i]
  have heq : sourceCovariance (IsingBulk.Branch.radialParameter d.alpha ε)
      (actualRegularCoordinates d B ε τ θ)=mixedCovariance (fun i => w (θ i)) (fun i => f (θ i)) := by
    simp only [sourceCovariance,hU,hv]
  rw [heq]
  convert hR using 1
  ring

end
end IsingBulk.HT22.Geometry

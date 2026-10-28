import IsingBulk.HT22.Geometry.SignedChartLift
import IsingBulk.HT22.Geometry.BalancedEqualityCharts

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.Preferred22 IsingBulk.First LocalLimit
open scoped Topology BigOperators

/-- Actual signed lifted contour integral localized in original free angles. -/
def localizedSignedLiftedIntegral (n : ℕ) (negative : Bool) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (χ : (Fin n → ℝ) → ℂ)
    (W : (Fin (n+1) → ℝ) → ℂ) (t : ℂ) : ℂ :=
  ∫ θ in angularBox n,
    let w := preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)
    χ θ*W w*Physical.complexSignedDensity negative (t,deformedAngles τ B.p B.m w)

theorem signed_equality_chart_radius (n : ℕ) (δ a : ℝ) (l : ℤ)
    (hc : (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)∈Ioo (-Real.pi-δ) (-Real.pi-δ+2*Real.pi))
    (hco : (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)∈Ioo (-Real.pi) Real.pi) :
    ∃ R : ℝ,0<R ∧ ∀ θ : Fin n → ℝ,
      ‖θ-(fun _ => (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ))‖<R →
      θ∈angularBox n ∧ preferredLiftedAngles δ (constrainedAtTotal a θ)=
        constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ := by
  obtain ⟨R,hR,hlift⟩ := signed_equality_lift_chart n δ a l hc
  let μ := (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)
  let ρ := min R (min (μ+Real.pi) (Real.pi-μ))
  have hρ : 0<ρ := lt_min hR (lt_min (by dsimp [μ]; linarith [hco.1]) (by dsimp [μ]; linarith [hco.2]))
  refine ⟨ρ,hρ,?_⟩
  intro θ hθ
  refine ⟨?_,hlift θ (hθ.trans_le (min_le_left _ _))⟩
  intro i _
  have hi : |θ i-μ|<ρ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using (norm_le_pi_norm (θ-(fun _ => μ)) i).trans_lt hθ
  have hρ1 : ρ≤μ+Real.pi := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ≤Real.pi-μ := (min_le_right _ _).trans (min_le_right _ _)
  have hh := abs_lt.mp hi
  constructor <;> linarith [hh.1,hh.2]

/-- Exact translation to the actual balanced shape integral, with the
eliminated-angle Lebesgue measure unchanged. -/
theorem localizedSignedLiftedIntegral_eq_chart (n : ℕ) (negative : Bool) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (l : ℤ) (R : ℝ)
    (hchart : ∀ θ : Fin n → ℝ,
      ‖θ-(fun _ => signedEqualityMean negative (n+1) l)‖<R →
      θ∈angularBox n ∧ preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)=
        constrainedAtTotal (Physical.constraintAngle negative+2*Real.pi*(l:ℝ)) θ)
    (χ : (Fin n → ℝ) → ℂ)
    (hsupp : ∀ θ,χ θ≠0 → ‖θ-(fun _ => signedEqualityMean negative (n+1) l)‖<R)
    (W : (Fin (n+1) → ℝ) → ℂ) (t : ℂ) :
    localizedSignedLiftedIntegral n negative d B τ χ W t =
      ∫ u : Fin n → ℝ,
        (χ (fun i => signedEqualityMean negative (n+1) l+u i)*
          W (fun i => signedEqualityMean negative (n+1) l+shapeExtend u i))*
        Physical.complexSignedDensity negative
          (t,balancedEqualityChart τ B.p B.m (signedEqualityMean negative (n+1) l) u) := by
  let μ := signedEqualityMean negative (n+1) l
  let c := Physical.constraintAngle negative+2*Real.pi*(l:ℝ)
  let F : (Fin n → ℝ) → ℂ := fun θ => χ θ*W (constrainedAtTotal c θ)*
    Physical.complexSignedDensity negative (t,deformedAngles τ B.p B.m (constrainedAtTotal c θ))
  have hF (θ : Fin n → ℝ) :
      (let w := preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)
       χ θ*W w*Physical.complexSignedDensity negative (t,deformedAngles τ B.p B.m w))=F θ := by
    by_cases hz : χ θ=0
    · simp only [hz,zero_mul,F]
    · dsimp only
      rw [(hchart θ (hsupp θ hz)).2]
  have hzero (θ : Fin n → ℝ) (hθ : θ∉angularBox n) : F θ=0 := by
    have hz : χ θ=0 := by
      by_contra hn
      exact hθ (hchart θ (hsupp θ hn)).1
    simp only [F,hz,zero_mul]
  unfold localizedSignedLiftedIntegral
  rw [show (fun θ => let w := preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)
      χ θ*W w*Physical.complexSignedDensity negative (t,deformedAngles τ B.p B.m w))=F from funext hF]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,←integral_add_right_eq_self F (fun _ => μ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    have hfun : u+(fun _ => μ)=(fun i => μ+u i) := by funext i; exact add_comm _ _
    have he : constrainedAtTotal c (u+(fun _ => μ))=fun i => μ+shapeExtend u i := by
      have hc : c/((n+1:ℕ):ℝ)=μ := by dsimp [c,μ,signedEqualityMean]; rw [add_comm]
      rw [hfun]
      simpa only [hc] using constrainedAtTotal_translate_mean n c u
    dsimp only [F]
    rw [he,hfun]
    rfl

end
end IsingBulk.HT22.Geometry

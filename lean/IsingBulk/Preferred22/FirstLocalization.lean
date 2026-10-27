import IsingBulk.Preferred22.PopulationObligations
import IsingBulk.Preferred22.FirstChart
import IsingBulk.Preferred22.RightDomain

/-! The actual lower first chart is untouched by the whole-contour
homotopy, has unit lower and right weights, and has the exact physical
normalization. This is an identity on a genuine open source neighborhood,
not an assertion that the complementary integral is bounded. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem preferred_lower_plateau_values (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {θ : ℝ} (hθ : θ∈Ioo (-Real.pi+B.delta) (-B.delta)) :
    B.p θ=0 ∧ B.m θ=1 ∧ deriv B.p θ=0 ∧ deriv B.m θ=0 := by
  have hp (x : ℝ) (hx : x∈Ioo (-Real.pi+B.delta) (-B.delta)) : B.p x=0 := by
    by_contra h
    have hpos := B.upper_support x ⟨by linarith [hx.1,B.delta_pos],by linarith [hx.2,B.delta_pos,Real.pi_pos]⟩ h
    linarith [hpos.1,hx.2,B.delta_pos]
  have hm (x : ℝ) (hx : x∈Ioo (-Real.pi+B.delta) (-B.delta)) : B.m x=1 := by
    exact B.plateau (-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hep : B.p=ᶠ[𝓝 θ] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact hp x hx
  have hem : B.m=ᶠ[𝓝 θ] (fun _ : ℝ => (1:ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact hm x hx
  exact ⟨hp θ hθ,hm θ hθ,by simpa only [deriv_const] using hep.deriv_eq,
    by simpa only [deriv_const] using hem.deriv_eq⟩

/-- Every entry of the full Jacobian is exactly the identity on the
lower plateau. In particular no residual determinant factor is omitted. -/
theorem preferred_first_plateau_matrix {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi+B.delta) (-B.delta)) :
    preferredContourMatrix τ B.p B.m θ=1 := by
  have h := fun i => preferred_lower_plateau_values d B (hθ i)
  ext i j
  simp only [preferredContourMatrix,shiftJacobian,(h i).1,(h i).2.1,
    (h i).2.2.1,(h i).2.2.2,(h j).2.2.1,(h j).2.2.2,
    mul_zero,sub_zero,add_zero,ite_self,Complex.ofReal_zero,Matrix.one_apply]

/-- On the lower plateau the literal deformed physical scalar is the
original scalar for every parameter, not merely asymptotically. -/
theorem preferred_first_plateau_density {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi+B.delta) (-B.delta)) :
    preferredDeformedPhysicalDensity τ B.p B.m s θ=fullAngularDensity s θ := by
  have hp : ∀ i, B.p (θ i)=0 := fun i => (preferred_lower_plateau_values d B (hθ i)).1
  have hP : occupancy B.p θ=0 := by simp [occupancy,hp]
  have hw (i : Fin N) : deformedAngles τ B.p B.m θ i=(θ i:ℂ) := by
    simp only [deformedAngles,balancedShift,hP,hp,zero_mul,mul_zero,sub_self,
      Complex.ofReal_zero,sub_zero]
  simp only [preferredDeformedPhysicalDensity,hw,← Complex.ofReal_cos,
    fullAngularDensity,angularRoots,angularW,angleRoot]
  rfl

/-- The exact normalized physical seed on the actual first chart.
The cutoff premise here is the true fixed right cutoff evaluated on the
configuration; the following neighborhood theorem discharges it. -/
theorem preferred_first_plateau_seed {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi+B.delta) (-B.delta)) (hr : ∀ i, r (θ i)=1) :
    preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m r s θ=
      fullAngularDensity s θ/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) := by
  have hp : ∀ i, B.p (θ i)=0 := fun i => (preferred_lower_plateau_values d B (hθ i)).1
  have hm : ∀ i, B.m (θ i)=1 := fun i => (preferred_lower_plateau_values d B (hθ i)).2.1
  have hP : occupancy B.p θ=0 := by simp [occupancy,hp]
  have hQ : occupancy B.m θ=(N:ℝ) := by simp [occupancy,hm]
  have hη0 : preferredPopulationCutoff 0=0 := preferredPopulationCutoff_zero (by norm_num)
  have hηN : preferredPopulationCutoff (N:ℝ)=1 := preferredPopulationCutoff_one (by
    have : (1:ℝ)≤N := by exact_mod_cast hN
    linarith)
  simp only [preferredPhysicalSeed,preferredCellWeight,preferredLowerWeight,
    lowerWeight,preferredRightWeight,hP,hQ,hη0,hηN,hr,Finset.prod_const_one]
  rw [preferred_first_plateau_matrix d B τ θ hθ,
    preferred_first_plateau_density d B τ s θ hθ,Matrix.det_one]
  norm_num

/-- The critical equal-angle point lies strictly to the right of the
inverse branch on the one-sided contour. -/
theorem preferred_alpha_lt_branch (d : PreferredBranchData) : d.alpha<d.b := by
  have hc : Real.cos d.alpha<1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0)
      (show d.alpha≤Real.pi by linarith [d.alpha_lt,Real.pi_pos]) d.alpha_pos
    simpa using h
  by_contra hn
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi d.b_pos.le
    (show d.alpha≤Real.pi by linarith [d.alpha_lt,Real.pi_pos]) (le_of_not_gt hn)
  rw [d.angle_relation] at hh
  linarith

/-- A fixed genuine neighborhood of -alpha lies in the untouched lower
plateau and in the unit part of the actual right cutoff. The neighborhood
is chosen before every particle number and deformation parameter. -/
theorem preferred_first_chart_seed_neighborhood (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB : ℝ) (r : ℝ → ℝ)
    (hr : PreferredRightCutoffData d B δB r) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
      (∀ i, |θ i+d.alpha|<ρ) → ∀ τ : ℝ, ∀ s : ℂ,
      preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m r s θ=
        fullAngularDensity s θ/((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) := by
  have h1 : 0<d.alpha-B.delta := by linarith [B.delta_alpha,d.alpha_pos]
  have h2 : 0<Real.pi-B.delta-d.alpha := by
    linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]
  have h3 : 0<d.b-d.alpha := sub_pos.mpr (preferred_alpha_lt_branch d)
  let ρ := min ((d.alpha-B.delta)/2)
    (min ((Real.pi-B.delta-d.alpha)/2) ((d.b-d.alpha)/2))
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ≤(d.alpha-B.delta)/2 := min_le_left _ _
  have hρ2 : ρ≤(Real.pi-B.delta-d.alpha)/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ≤(d.b-d.alpha)/2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,hρ,?_⟩
  intro N hN θ hθ τ s
  have hw (i : Fin N) : θ i∈Ioo (-Real.pi+B.delta) (-B.delta) := by
    obtain ⟨hlo,hhi⟩ := abs_lt.mp (hθ i)
    constructor <;> linarith
  apply preferred_first_plateau_seed hN d B τ r s θ hw
  intro i
  have hi := abs_lt.mp (hθ i)
  apply (hr.2.2.2.2.2 (θ i)
    ⟨by linarith [(hw i).1,B.delta_pos],by linarith [(hw i).2,B.delta_pos]⟩).2
  linarith [hr.1]

/-- The localized physical shape integral is literally the localized right
transport seed on the same real hyperplane, including N! and Haar measure.
Its cutoff is allowed to be any of the actual compact smooth shape cutoffs
supported in the proved common lower-chart neighborhood. -/
theorem preferred_localized_integral_eq_right_seed (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (δB : ℝ) (r : ℝ → ℝ)
    (hr : PreferredRightCutoffData d B δB r) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ n : ℕ, ∀ chi : IsingBulk.First.ShapeSpace n → ℂ,
      (∀ t : Fin n → ℝ,
        chi (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))≠0 →
          ∀ i, |firstChartAngles d.alpha t i+d.alpha|<ρ) →
      ∀ τ : ℝ, ∀ s : ℂ,
      localizedPhysicalIntegral d.alpha chi s=
        ∫ t : Fin n → ℝ,
          chi (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))*
            preferredPhysicalSeed .right τ preferredPopulationCutoff B.p B.m r s
              (firstChartAngles d.alpha t) := by
  obtain ⟨ρ,hρ,hsource⟩ := preferred_first_chart_seed_neighborhood d B δB r hr
  refine ⟨ρ,hρ,?_⟩
  intro n chi hchi τ s
  unfold localizedPhysicalIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hz : chi (IsingBulk.First.shapeCoordinateEquiv n (WithLp.toLp 2 t))=0
  · simp only [hz,zero_mul]
  · rw [hsource (n+1) (by omega) (firstChartAngles d.alpha t) (hchi t hz) τ s]
    simp only [Nat.add_sub_cancel,div_eq_mul_inv]
    ring

end
end IsingBulk.Preferred22

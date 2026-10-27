import IsingBulk.Preferred22.CoordinateShell

/-! The actual q23 bounds at the complete configuration diameter. The
constant precedes particle count and actual occupancies. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology

theorem preferredAngularDiameter_pair_le {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) :
    |θ i-θ j| ≤ preferredAngularDiameter θ := by
  simpa only [Real.dist_eq,preferredAngularDiameter] using
    Metric.dist_le_diam_of_mem (Set.finite_range θ).isBounded (Set.mem_range_self i) (Set.mem_range_self j)

/-- Every actual regular coordinate times any coordinate separation is
controlled by the original complete angular diameter. This is the uniform
scale cancellation needed for the collective parameter jets. -/
theorem preferred_actual_coordinate_diameter_product (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ v,-δB ≤ θ v+d.b ∧ θ v+d.b ≤ d.b+B.delta) →
      0 < preferredAngularDiameter θ → ∀ v i j : Fin N,
      ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ v‖ *
        ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i-
          preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ j‖ ≤
        C*preferredAngularDiameter θ := by
  obtain ⟨Ca,εa,τa,δa,hCa,hεa,hτa,hδa,hδaδ,ha⟩ := preferred_actual_coordinate_absolute_scale d B
  obtain ⟨Cd,εd,τd,δd,hCd,hεd,hτd,hδd,_,hd⟩ := preferred_actual_coordinate_difference d B
  refine ⟨Ca*Cd,min εa εd,min τa τd,min δa δd,mul_pos hCa hCd,
    lt_min hεa hεd,lt_min hτa hτd,lt_min hδa hδd,(min_le_left _ _).trans_lt hδaδ,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hbox hD v i j
  let z : Fin N := ⟨0,hN⟩
  let D := preferredAngularDiameter θ
  let t := θ z+d.b
  have hwindow (a : Fin N) : t-2*D ≤ θ a+d.b ∧ θ a+d.b ≤ t+2*D := by
    have hh := abs_le.mp (preferredAngularDiameter_pair_le θ a z)
    dsimp [t,D]
    constructor <;> linarith [hh.1,hh.2]
  have hboxa (a : Fin N) : -δa ≤ θ a+d.b ∧ θ a+d.b ≤ d.b+B.delta :=
    ⟨le_trans (neg_le_neg (min_le_left _ _)) (hbox a).1,(hbox a).2⟩
  have hboxd (a : Fin N) : -δd ≤ θ a+d.b ∧ θ a+d.b ≤ d.b+B.delta :=
    ⟨le_trans (neg_le_neg (min_le_right _ _)) (hbox a).1,(hbox a).2⟩
  have hqa := ha N hN ε τ t D hε (hεr.trans_le (min_le_left _ _)) hτ
    (hτr.trans_le (min_le_left _ _)) hD θ hboxa hwindow v
  have hqd := hd N hN ε τ t D hε (hεr.trans_le (min_le_right _ _)) hτ
    (hτr.trans_le (min_le_right _ _)) hD θ hboxd hwindow i j
  have hs : 0 < Real.sqrt (|t|+D+ε) := Real.sqrt_pos.2 (by positivity)
  calc
    _ ≤ (Ca*Real.sqrt (|t|+D+ε))*(Cd*D/Real.sqrt (|t|+D+ε)) :=
      mul_le_mul hqa hqd (norm_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

/-- Endpoint-maximum form of the same literal source estimate. -/
theorem preferred_actual_coordinate_diameter_max_product (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ N : ℕ, 0 < N → ∀ ε τ : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ v,-δB ≤ θ v+d.b ∧ θ v+d.b ≤ d.b+B.delta) →
      0 < preferredAngularDiameter θ → ∀ i j : Fin N,
      max ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖
        ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ j‖ *
        ‖preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i-
          preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ j‖ ≤
        C*preferredAngularDiameter θ := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hb⟩ := preferred_actual_coordinate_diameter_product d B
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hbox hD i j
  rw [max_mul_of_nonneg _ _ (norm_nonneg _)]
  exact max_le (hb N hN ε τ hε hεr hτ hτr θ hbox hD i i j)
    (hb N hN ε τ hε hεr hτ hτr θ hbox hD j i j)

end
end IsingBulk.Preferred22

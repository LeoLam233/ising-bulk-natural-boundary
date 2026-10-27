import IsingBulk.Preferred22.SourceCollectiveNeighborhood
import IsingBulk.Preferred22.ContourInverseBounds
import IsingBulk.Preferred22.ZerothSourceBound

/-! The literal physical angular transport field has only one inverse
configuration diameter. The estimate uses the actual matrix inverse and
actual collective field, uniformly before particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- A fixed bound for the inverse occupancy matrix transfers the actual
collective field estimate into the physical angular representative. -/
theorem preferredAngularRepresentative_norm_bound {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (ud uq b : Fin N → ℂ) {A L H : ℝ}
    (hA : 0≤A) (hL : 0≤L) (hH : 0≤H)
    (hM : ∀ x : Fin N → ℂ,‖M⁻¹.mulVec x‖≤A*‖x‖)
    (hud : ∀ i,‖ud i‖≤L) (huq : ∀ i,‖uq i‖≤L) (hb : ‖b‖≤H) (i : Fin N) :
    ‖preferredAngularRepresentative M ud uq b i‖≤A*(L+L*H) := by
  have hx : ‖(fun j => ud j+uq j*b j)‖≤L+L*H := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    calc
      _ ≤ ‖ud j‖+‖uq j*b j‖ := norm_add_le _ _
      _ = ‖ud j‖+‖uq j‖*‖b j‖ := by rw [norm_mul]
      _ ≤ L+L*H := add_le_add (hud j) (mul_le_mul (huq j)
        ((norm_le_pi_norm b j).trans hb) (norm_nonneg _) hL)
  unfold preferredAngularRepresentative
  rw [norm_neg]
  exact (norm_le_pi_norm _ i).trans ((hM _).trans (mul_le_mul_of_nonneg_left hx hA))

/-- True source V_i=O(N^2/diameter) on the full actual right contour.
No field bound, denominator margin or occupancy independence is assumed. -/
theorem preferred_actual_angular_field_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ C ε₀ τ₀ δB : ℝ,0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,θ∈preferredRightAngularBox d B.delta δB N →
      0<preferredAngularDiameter θ → ∀ i : Fin N,
      ‖preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
        C*(N:ℝ)^2/preferredAngularDiameter θ := by
  obtain ⟨cb,hcb,_hcba,hbsource⟩ := preferred_actual_collective_neighborhood d
  obtain ⟨cu,ρ,c,D,hcu,hcua,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  let cap := min cb cu
  refine ⟨cap,lt_min hcb hcu,(min_le_right _ _).trans_lt hcua,?_⟩
  intro B hBcap
  obtain ⟨η,M,εb,τb,δb,hη,hM,hεb,hτb,hδb,hδbδ,hb⟩ :=
    hbsource B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨L,hL,hLu⟩ := preferred_compact_collective_bounds d ρ c D hρ hDc hgood
  obtain ⟨τm,hτm,hm⟩ := preferredContourMatrix_uniform_half_row B.p B.m B.smooth B.m_smooth
    B.periodic B.m_periodic
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound (-x))]; exact B.upper_bound (-x))
  let ε₀ := min εb (min r (ρ/2))
  let τ₀ := min τb (min r τm)
  let δB := min δb (min (r/2) (B.delta/2))
  let C := 4*L*(2*Real.pi+M)
  have hδB : 0<δB := lt_min hδb (lt_min (half_pos hr) (half_pos B.delta_pos))
  have hδBδ : δB<B.delta := (min_le_left _ _).trans_lt hδbδ
  refine ⟨C,ε₀,τ₀,δB,by dsimp [C]; positivity,lt_min hεb (lt_min hr (half_pos hρ)),
    lt_min hτb (lt_min hr hτm),hδB,hδBδ,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam i
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hεb' : ε<εb := hεr.trans_le (min_le_left _ _)
  have hεr' : ε<r := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hερ : ε≤ρ/2 := (hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hτb' : τ<τb := hτr.trans_le (min_le_left _ _)
  have hτr' : τ<r := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτm' : τ≤τm := (hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hboxb (a : Fin N) : -δb≤θ a+d.b ∧ θ a+d.b≤d.b+B.delta := by
    have hh := hθ a
    have hd : δB≤δb := min_le_left _ _
    constructor <;> linarith [hh.1,hh.2]
  have hB : ‖preferredResidualCollective s q‖≤M*(N:ℝ)^2/preferredAngularDiameter θ := by
    have hh := (hb N hN ε τ hε hεb' hτ hτb' θ hboxb hdiam).2 0 (by simp)
    simpa only [preferredRescaledCollective,Prod.fst_zero,Prod.snd_zero,mul_zero,
      smul_zero,add_zero] using hh
  have hsd : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact hερ
  have hq (a : Fin N) : q a∈D := by
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ a)
      (by simpa only [abs_of_pos hε] using hεr')
      (by simpa only [abs_of_nonneg hτ] using hτr')
      (preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ)
      (preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ)
      (by have hh := (hθ a).1; have hd : δB≤r/2 := (min_le_right _ _).trans (min_le_left _ _); linarith)
      ((hθ a).2.trans (hBcap.trans_le (min_le_right _ _)).le)
    rw [preferredBumpCoordinate_actual] at hh
    exact interior_subset hh
  have hMinv := (preferred_matrix_inverse_of_row_three_quarters (preferredContourMatrix τ B.p B.m θ)
    (fun a => (hm τ hτ hτm' N hN θ a).trans (by norm_num))).2
  have hv := preferredAngularRepresentative_norm_bound (preferredContourMatrix τ B.p B.m θ)
    (fun a => preferredSourceUDot s (q a)) (fun a => preferredSourceUQ s (q a))
    (preferredResidualCollective s q) (by norm_num : (0:ℝ)≤4) (by linarith : 0≤L)
    (by positivity : 0≤M*(N:ℝ)^2/preferredAngularDiameter θ) hMinv
    (fun a => (hLu s (q a) hsd (hq a)).2.1) (fun a => (hLu s (q a) hsd (hq a)).1) hB i
  have hdπ : preferredAngularDiameter θ≤2*Real.pi := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    rw [Real.dist_eq]
    apply abs_le.mpr
    have ha := hθ a
    have hb := hθ b
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,B.branch_plateau,B.delta_b,d.b_lt]
  have hN1 : (1:ℝ)≤(N:ℝ)^2 := by
    have hh : (1:ℝ)≤N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN)
    nlinarith
  change ‖preferredAngularRepresentative (preferredContourMatrix τ B.p B.m θ)
    (fun a => preferredSourceUDot s (q a)) (fun a => preferredSourceUQ s (q a))
    (preferredResidualCollective s q) i‖≤_
  calc
    _ ≤ 4*(L+L*(M*(N:ℝ)^2/preferredAngularDiameter θ)) := hv
    _ = 4*L*(preferredAngularDiameter θ+M*(N:ℝ)^2)/preferredAngularDiameter θ := by field_simp
    _ ≤ 4*L*((2*Real.pi+M)*(N:ℝ)^2)/preferredAngularDiameter θ := by
      apply div_le_div_of_nonneg_right _ hdiam.le
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤4*L)
      nlinarith [mul_le_mul_of_nonneg_left hN1 (by positivity : 0≤2*Real.pi)]
    _ = C*(N:ℝ)^2/preferredAngularDiameter θ := by dsimp [C]; ring

end
end IsingBulk.Preferred22

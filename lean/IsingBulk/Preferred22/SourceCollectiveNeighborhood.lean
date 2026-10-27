import IsingBulk.Preferred22.CollectiveNeighborhood
import IsingBulk.Preferred22.CoordinateDiameter
import IsingBulk.Preferred22.BalancedPairGeometry

/-! The collective analytic neighborhood is constructed for the literal
balanced source, uniformly before particle count, radial parameter and
configuration. Every geometric and scalar bound is proved from the source. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Rescaling the genuine field, with independent parameter and q radii. -/
def preferredRescaledCollective {N : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (η d : ℝ) (z : ℂ × (Fin N → ℂ)) : Fin N → ℂ :=
  preferredResidualCollective (s+((η/(N:ℝ)^2:ℝ):ℂ)*z.1)
    (q+((η*d/(N:ℝ)^2:ℝ):ℂ) • z.2)

/-- Complete actual source neighborhood. The field is not replaced by an
arbitrary function, and neither an R margin nor a field estimate is assumed. -/
theorem preferred_actual_collective_neighborhood (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ η M ε₀ τ₀ δB : ℝ, 0<η ∧ 0<M ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        let s := IsingBulk.Branch.radialParameter d.alpha ε
        let q := preferredSourceCoordinate τ B.p B.m s θ
        AnalyticOnNhd ℂ (preferredRescaledCollective s q η (preferredAngularDiameter θ))
          (ball 0 1) ∧
        ∀ z∈ball (0 : ℂ × (Fin N → ℂ)) 1,
          ‖preferredRescaledCollective s q η (preferredAngularDiameter θ) z‖≤
            M*(N:ℝ)^2/preferredAngularDiameter θ := by
  obtain ⟨cap,ρ,c,D,hcap,hcapa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain_with_margin d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  have hU (s q : ℂ) (hs : ‖s-preferredSelectedPoint d‖<ρ) (hq : q∈D) :
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) :=
    (hgood s q q hs hq hq).2.1
  obtain ⟨R,hR,hRρ,hpair⟩ := preferred_global_parameter_pair_bound d ρ D hρ hDc hDv
    (interior_subset hzero) hU
  obtain ⟨A₀,hA₀,hpair₀⟩ := hpair 0
  obtain ⟨A₁,hA₁,hpair₁⟩ := hpair 1
  obtain ⟨L,hL,hLb⟩ := preferred_compact_collective_bounds d ρ c D hρ hDc hgood
  obtain ⟨κ,r, hκ,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨Q,εq,τq,δq,hQ,hεq,hτq,hδq,hδqB,hqscale⟩ :=
    preferred_actual_coordinate_diameter_max_product d B
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  obtain ⟨τg,hτg,hgeom⟩ := balanced_source_collective_geometry B.p B.m
    B.smooth B.m_smooth B.periodic hmp
  obtain ⟨εg,hεg,hmargin⟩ := preferred_radial_one_sided_margins d B.delta B.delta_pos
    (B.delta_alpha.trans (by linarith [d.alpha_pos]))
  let C := max L (max (A₀*Q) (A₁*Q))
  have hC : 1≤C := hL.trans (le_max_left _ _)
  have hC0 : 0<C := lt_of_lt_of_le (by norm_num) hC
  have hLC : L≤C := le_max_left _ _
  have hA₀C : A₀*Q≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hA₁C : A₁*Q≤C := (le_max_right _ _).trans (le_max_right _ _)
  let η := min 1 (min (R/2) (min (κ/(2*Real.pi)) ((3/8:ℝ)/(16*C^2))))
  have hη : 0<η := lt_min (by norm_num) (lt_min (half_pos hR)
    (lt_min (by positivity) (by positivity)))
  have hη1 : η≤1 := min_le_left _ _
  have hηR : η≤R/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηκ : η*(2*Real.pi)≤κ := (le_div_iff₀ (by positivity)).mp
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηr : η≤(3/8:ℝ)/(16*C^2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let M := C*(2*Real.pi)+8*C^3*(1+C)/(c*(3/8:ℝ))
  have hM : 0<M := by dsimp [M]; positivity
  let ε₀ := min r (min (R/2) (min εq εg))
  let τ₀ := min r (min τq τg)
  let δB := min δq (r/2)
  have hε₀ : 0<ε₀ := lt_min hr (lt_min (half_pos hR) (lt_min hεq hεg))
  have hτ₀ : 0<τ₀ := lt_min hr (lt_min hτq hτg)
  have hδB : 0<δB := lt_min hδq (half_pos hr)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt hδqB
  refine ⟨η,M,ε₀,τ₀,δB,hη,hM,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro N hN ε τ hε hεsmall hτ hτsmall θ hθ hdiam
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  let diam := preferredAngularDiameter θ
  have hs : ‖s-preferredSelectedPoint d‖≤R/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact (hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hepsr : ε<r := hεsmall.trans_le (min_le_left _ _)
  have hepsq : ε<εq := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsg : ε<εg := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hτr : τ<r := hτsmall.trans_le (min_le_left _ _)
  have hτq' : τ<τq := hτsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτg' : τ≤τg := (hτsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hqmargin (i : Fin N) : closedBall (q i) κ⊆D := by
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hepsr)
      (by simpa only [abs_of_nonneg hτ] using hτr)
      (preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ)
      (preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ)
      (by have := (hθ i).1; have := min_le_right δq (r/2); dsimp [δB] at *; linarith)
      (by have := (hθ i).2; linarith)
    simpa only [preferredBumpCoordinate_actual] using hh
  have hqD (i : Fin N) : q i∈D := hqmargin i (mem_closedBall_self hκ.le)
  have hscale (i j : Fin N) : max ‖q i‖ ‖q j‖*‖q i-q j‖≤Q*diam := by
    apply hqscale N hN ε τ hε hepsq hτ hτq' θ _ hdiam i j
    intro v
    exact ⟨le_trans (neg_le_neg (min_le_left _ _)) (hθ v).1,(hθ v).2⟩
  have hpairbase (i j : Fin N) :
      ‖preferredMovingInverse s (q i)-preferredMovingInverse s (q j)‖≤C*diam := by
    have hh := hpair₀ s (q i) (q j) (hs.trans (by linarith)) (hqD i) (hqD j)
    simp only [iteratedDeriv_zero] at hh
    calc
      _ ≤ A₀*max ‖q i‖ ‖q j‖*‖q i-q j‖ := hh
      _ ≤ A₀*(Q*diam) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hscale i j) hA₀.le
      _ ≤ C*diam := by nlinarith [mul_le_mul_of_nonneg_right hA₀C hdiam.le]
  have hpairder (t : ℂ) (i j : Fin N) (ht : ‖t-preferredSelectedPoint d‖≤R) :
      ‖deriv (fun v => preferredMovingInverse v (q i)-preferredMovingInverse v (q j)) t‖≤C*diam := by
    have hh := hpair₁ t (q i) (q j) ht (hqD i) (hqD j)
    simp only [iteratedDeriv_one] at hh
    calc
      _ ≤ A₁*max ‖q i‖ ‖q j‖*‖q i-q j‖ := hh
      _ ≤ A₁*(Q*diam) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hscale i j) hA₁.le
      _ ≤ C*diam := by nlinarith [mul_le_mul_of_nonneg_right hA₁C hdiam.le]
  obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hepsg
  have hθπ (i : Fin N) : θ i∈Icc (-Real.pi-B.delta) B.delta := by
    have hh := hθ i
    constructor <;> linarith [B.branch_plateau,hδBB]
  have hgeom' := hgeom τ hτ hτg' N hN θ s B.delta B.delta_pos
    (B.delta_alpha.trans (by linarith [d.alpha_lt])) hSr hSi hSδ hθπ
    B.lower_bound (fun x => B.lower_bound (-x))
    (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx)
  have hbaseR : (3/8:ℝ)*diam^2≤‖collectiveDenominator (fun i => preferredMovingInverse s (q i))‖ := hgeom'.1
  have hdiammax : diam≤2*Real.pi := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rw [Real.dist_eq]
    apply abs_le.mpr
    have hi := hθ i
    have hj := hθ j
    constructor <;> linarith [B.branch_plateau,B.delta_alpha,d.alpha_lt,hδBB]
  have hball (z : ℂ × (Fin N → ℂ)) (hz : z∈ball 0 1) :
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
        (s+((η/(N:ℝ)^2:ℝ):ℂ)*z.1,q+((η*diam/(N:ℝ)^2:ℝ):ℂ) • z.2) ∧
      ‖preferredRescaledCollective s q η diam z‖≤M*(N:ℝ)^2/diam := by
    have hz' : ‖z‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hz₁ : ‖z.1‖≤1 := (le_max_left _ _).trans hz'.le
    have hz₂ : ‖z.2‖≤1 := (le_max_right _ _).trans hz'.le
    apply preferred_collective_scaled_neighborhood hN (preferredSelectedPoint d) s _ q _ D
      R κ C c (3/8) diam (2*Real.pi) η hR hκ hC hc (by norm_num) hdiam hdiammax
      hη hη1 hηR hηκ hηr hDv hs hqmargin
    · intro t v ht hv
      exact hU t v (by linarith) hv
    · intro t ht
      exact (hgood t 0 0 (by linarith) (interior_subset hzero) (interior_subset hzero)).1
    · intro t v ht hv
      exact ((hLb t v (ht.trans hRρ) hv).1).trans hLC
    · intro t v ht hv
      exact ((hLb t v (ht.trans hRρ) hv).2.1).trans hLC
    · intro t ht
      exact ((hLb t 0 (ht.trans hRρ) (interior_subset hzero)).2.2).trans hLC
    · intro t v ht hv
      have hh := hgood t v v (by linarith) hv hv
      change c≤(deriv (deriv (preferredMovingInverse t)) v).re
      rw [←preferredMovingCurvature_eq_deriv t v hh.2.1]
      exact hh.2.2.2.1.le
    · exact hpairbase
    · exact hpairder
    · exact hbaseR
    · simp only [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0≤η/(N:ℝ)^2)]
      exact mul_le_of_le_one_right (by positivity) hz₁
    · simp only [add_sub_cancel_left,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0≤η*diam/(N:ℝ)^2)]
      exact mul_le_of_le_one_right (by positivity) hz₂
  constructor
  · intro z hz
    apply AnalyticAt.comp (g:=fun x : ℂ × (Fin N → ℂ) => preferredResidualCollective x.1 x.2)
      (f:=fun x : ℂ × (Fin N → ℂ) =>
        (s+((η/(N:ℝ)^2:ℝ):ℂ)*x.1,q+((η*diam/(N:ℝ)^2:ℝ):ℂ) • x.2)) (hball z hz).1
    exact (analyticAt_const.add (analyticAt_const.mul analyticAt_fst)).prod
      (analyticAt_const.add
        ((((η*diam/(N:ℝ)^2:ℝ):ℂ) • ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)).analyticAt z))
  · exact fun z hz => (hball z hz).2

end
end IsingBulk.Preferred22

import IsingBulk.Preferred22.LowerEqualityDisks
import IsingBulk.Preferred22.InnerEqualitySupport
import IsingBulk.Preferred22.WeightedBoundaryCauchy

/-! Uniform actual complex derivatives of the complete lower-order equality
tube. All constrained integer means and N=2 are retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem preferred_radialParameter_distance (d : PreferredBranchData)
    {ε : ℝ} (hε : 0≤ε) :
    ‖IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d‖=ε := by
  have he : IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d=
      (ε:ℂ)*Complex.exp ((d.alpha:ℂ)*Complex.I) := by
    simp only [preferredSelectedPoint,IsingBulk.Branch.radialParameter,add_zero,
      Complex.ofReal_one,one_mul,Complex.ofReal_add]
    ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hε]

/-- The tube radius, deformation scale and radial scale are chosen before
the derivative order. The integral is the literal normalized physical
right seed with the complementary smooth equality multiplier. -/
theorem preferred_actual_lower_inner_derivative_bound (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ)
    (hEven : Even (n+1)) (hNp : n+1<2*p) (B : PreferredCoareaBump d) :
    ∃ δ₀ R₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ 0<R₀ ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,δB≤δ₀ → ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ R τ : ℝ,0<R → R≤R₀ → 0≤τ → τ<τ₀ →
      ∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredWeightedRightIntegral n d B
          (fun θ => 1-preferredEqualityMultiplier R θ) τ rcut 0)
            (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C := by
  obtain ⟨g,hg,hgeom⟩ := preferred_finite_equality_tube_geometry d hp ha hα
    (by omega : 0<n+1)
  obtain ⟨r,M,hr,hM,hdisks⟩ := preferred_lower_equal_density_uniform_disks d hp hp5 ha hα
    (by omega : 0<n+1) hEven hNp hg (by linarith [B.delta_b,d.b_pos] : B.delta<d.b)
  obtain ⟨J,hJ,hjac⟩ := preferred_contour_determinant_bound d B
  refine ⟨g/4,min (g/4) (r/4),min 1 (r/4),r/4,by positivity,
    lt_min (by positivity) (by positivity),lt_min (by norm_num) (by positivity),by positivity,?_⟩
  intro δB hδB rcut hcut R τ hR hRR hτ hτr j
  let C := (J^(n+1)/(((n+1).factorial:ℝ)*(2*Real.pi)^n))*
    ((j.factorial:ℝ)*M/(r/4)^j)*(2*Real.pi)^n+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ε hε hεr
  have hRr : R≤r/4 := hRR.trans (min_le_right _ _)
  have hRg : R≤g/4 := hRR.trans (min_le_left _ _)
  have hτr' : τ<r/4 := hτr.trans_le (min_le_right _ _)
  have hτ1 : τ≤1 := (hτr.trans_le (min_le_left _ _)).le
  have hpoint : ∀ θ∈angularBox n,
      let w := preferredLiftedAngles B.delta (constrainedAngles θ)
      (1-preferredEqualityMultiplier R w)*
        (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)≠0 →
      AnalyticOnNhd ℂ (fun t : ℂ => preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m w))
        (closedBall (IsingBulk.Branch.radialParameter d.alpha ε) (r/4)) ∧
      ∀ t∈closedBall (IsingBulk.Branch.radialParameter d.alpha ε) (r/4),
        ‖preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m w)‖≤M := by
    intro θ hθ
    dsimp only
    intro hw
    let w := preferredLiftedAngles B.delta (constrainedAngles θ)
    obtain ⟨hreg,hdiam⟩ := preferred_inner_right_support d B hR rcut hcut θ hθ hw
    obtain ⟨l,_hl,ht,hwindow,_hmargin⟩ := hgeom B n le_rfl δB hδB θ hreg (hdiam.trans hRg)
    obtain ⟨ha,hb⟩ := hdisks l ht
    have hang : ‖deformedAngles τ B.p B.m w-
        (fun _ : Fin (n+1) => (IsingBulk.PrimeFamily.angle (n+1) l:ℂ))‖≤r := by
      exact (preferred_deformedAngles_distance_equal (by omega) d B hτ w _ hR.le
        (fun i => (hwindow i).trans hdiam)).trans (by linarith)
    have hmem (t : ℂ) (ht : t∈closedBall (IsingBulk.Branch.radialParameter d.alpha ε) (r/4)) :
        (t,deformedAngles τ B.p B.m w)∈closedBall
          (preferredSelectedPoint d,fun _ : Fin (n+1) => (IsingBulk.PrimeFamily.angle (n+1) l:ℂ)) r := by
      have ht' : ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤r/4 :=
        by simpa only [mem_closedBall,dist_eq_norm] using ht
      have hs : ‖t-preferredSelectedPoint d‖≤r := by
        calc
          _ = ‖(t-IsingBulk.Branch.radialParameter d.alpha ε)+
              (IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d)‖ := by
            congr 1
            ring
          _ ≤ ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖+
              ‖IsingBulk.Branch.radialParameter d.alpha ε-preferredSelectedPoint d‖ := norm_add_le _ _
          _ ≤ r := by rw [preferred_radialParameter_distance d hε.le]; linarith
      simpa only [mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,max_le_iff]
        using And.intro hs hang
    constructor
    · intro t ht'
      exact AnalyticAt.comp (f := fun t : ℂ => (t,deformedAngles τ B.p B.m w))
        (g := @preferredBoundaryAngularDensity (n+1)) (ha _ (hmem t ht'))
        (analyticAt_id.prod analyticAt_const)
    · intro t ht'
      exact hb _ (hmem t ht')
  have hb := preferred_weighted_right_derivative_from_boundary_disk n d B hε hτ
    (by positivity : 0<r/4) (by linarith : 0≤M) (by positivity : 0≤J^(n+1))
    (fun θ => 1-preferredEqualityMultiplier R θ) (preferredInnerEqualityMultiplier_smooth R)
    rcut hcut.2.2.1 j (preferred_inner_right_weight_norm d B rcut hcut R)
    (hjac (n+1) (by omega) τ hτ hτ1) hpoint
  exact hb.trans (by dsimp only [C]; linarith)

end
end IsingBulk.Preferred22

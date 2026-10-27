import IsingBulk.Preferred22.FirstEqualityDisks
import IsingBulk.Preferred22.LowerInnerIntegral

/-! The complete noncritical inner equality contribution at the first
prime order has bounded actual derivatives. A second equality radius is
chosen inside the original multiplier's critical zero neighborhood. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_first_inner_factor_derivative_bound (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ) (hN : n+1=2*p)
    (B : PreferredCoareaBump d) :
    ∃ δ₀ R₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ 0<R₀ ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,δB≤δ₀ → ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ σ : (Fin (n+1) → ℝ) → ℂ,ContDiff ℝ ∞ σ → (∀θ,‖σ θ‖≤1) →
      ∀ κ : ℝ,0<κ → (∀θ : Fin (n+1) → ℝ,(∀i,|θ i+d.alpha|<κ) → σ θ=0) →
      ∀ R τ : ℝ,0<R → R≤R₀ → R<κ → 0≤τ → τ<τ₀ →
      ∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (preferredWeightedRightIntegral n d B
          (fun θ => (1-preferredEqualityMultiplier R θ)*σ θ) τ rcut 0)
            (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C := by
  obtain ⟨g,hg,hgeom⟩ := preferred_finite_equality_tube_geometry d hp ha hα (by omega : 0<n+1)
  have hdisk : ∃ r M : ℝ,0<r ∧ 1≤M ∧ ∀l : ℤ,
      IsingBulk.PrimeFamily.angle (n+1) l∈Icc (-d.b+g) B.delta →
      IsingBulk.PrimeFamily.angle (n+1) l≠ -d.alpha →
      AnalyticOnNhd ℂ (@preferredBoundaryAngularDensity (n+1))
        (closedBall (preferredSelectedPoint d,fun _ : Fin (n+1) => (IsingBulk.PrimeFamily.angle (n+1) l:ℂ)) r) ∧
      ∀x∈closedBall (preferredSelectedPoint d,fun _ : Fin (n+1) => (IsingBulk.PrimeFamily.angle (n+1) l:ℂ)) r,
        ‖preferredBoundaryAngularDensity x‖≤M := by
    rw [hN]
    exact preferred_first_noncritical_density_uniform_disks d hp hp5 ha hα hg B.delta_pos.le
      (by linarith [B.delta_b,d.b_pos]) B.delta_alpha
  obtain ⟨r,M,hr,hM,hdisks⟩ := hdisk
  obtain ⟨J,hJ,hjac⟩ := preferred_contour_determinant_bound d B
  refine ⟨g/4,min (g/4) (r/4),min 1 (r/4),r/4,by positivity,
    lt_min (by positivity) (by positivity),lt_min (by norm_num) (by positivity),by positivity,?_⟩
  intro δB hδB rcut hcut σ hσ hσb κ _hκ hσzero R τ hR hRR hRκ hτ hτr j
  let C := (J^(n+1)/(((n+1).factorial:ℝ)*(2*Real.pi)^n))*
    ((j.factorial:ℝ)*M/(r/4)^j)*(2*Real.pi)^n+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ε hε hεr
  have hRr : R≤r/4 := hRR.trans (min_le_right _ _)
  have hRg : R≤g/4 := hRR.trans (min_le_left _ _)
  have hτr' : τ<r/4 := hτr.trans_le (min_le_right _ _)
  have hτ1 : τ≤1 := (hτr.trans_le (min_le_left _ _)).le
  have hpoint : ∀θ∈angularBox n,
      let w := preferredLiftedAngles B.delta (constrainedAngles θ)
      ((1-preferredEqualityMultiplier R w)*σ w)*
        (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)≠0 →
      AnalyticOnNhd ℂ (fun t : ℂ => preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m w))
        (closedBall (IsingBulk.Branch.radialParameter d.alpha ε) (r/4)) ∧
      ∀t∈closedBall (IsingBulk.Branch.radialParameter d.alpha ε) (r/4),
        ‖preferredBoundaryAngularDensity (t,deformedAngles τ B.p B.m w)‖≤M := by
    intro θ hθ
    dsimp only
    intro hw
    let w := preferredLiftedAngles B.delta (constrainedAngles θ)
    have hσw : σ w≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2
    have hiw : (1-preferredEqualityMultiplier R w)*
        (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)≠0 :=
      mul_ne_zero (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1 (mul_ne_zero_iff.mp hw).2
    obtain ⟨hreg,hdiam⟩ := preferred_inner_right_support d B hR rcut hcut θ hθ hiw
    obtain ⟨l,_hl,ht,hwindow,_hmargin⟩ := hgeom B n le_rfl δB hδB θ hreg (hdiam.trans hRg)
    have hnoncritical : IsingBulk.PrimeFamily.angle (n+1) l≠ -d.alpha := by
      intro hc
      apply hσw
      apply hσzero
      intro i
      have hh := (hwindow i).trans_lt (hdiam.trans_lt hRκ)
      simpa only [hc,sub_neg_eq_add] using hh
    obtain ⟨ha,hb⟩ := hdisks l ht hnoncritical
    have hang : ‖deformedAngles τ B.p B.m w-
        (fun _ : Fin (n+1) => (IsingBulk.PrimeFamily.angle (n+1) l:ℂ))‖≤r :=
      (preferred_deformedAngles_distance_equal (by omega) d B hτ w _ hR.le
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
  have hweight (θ : Fin (n+1) → ℝ) :
      ‖((1-preferredEqualityMultiplier R θ)*σ θ)*
        (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut θ:ℂ)‖≤1 := by
    calc
      _ = ‖σ θ‖*‖(1-preferredEqualityMultiplier R θ)*
          (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut θ:ℂ)‖ := by
        simp only [norm_mul]
        ring
      _ ≤ 1*1 := mul_le_mul (hσb θ) (preferred_inner_right_weight_norm d B rcut hcut R θ)
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hb := preferred_weighted_right_derivative_from_boundary_disk n d B hε hτ
    (by positivity : 0<r/4) (by linarith : 0≤M) (by positivity : 0≤J^(n+1))
    (fun θ => (1-preferredEqualityMultiplier R θ)*σ θ)
    ((preferredInnerEqualityMultiplier_smooth R).mul hσ) rcut hcut.2.2.1 j hweight
    (hjac (n+1) (by omega) τ hτ hτ1) hpoint
  exact hb.trans (by dsimp only [C]; linarith)

end
end IsingBulk.Preferred22

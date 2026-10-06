import IsingBulk.Tail.DeformedPointRealJets
import IsingBulk.Tail.MixedCompactPairJets

/-! Uniform real jets after pulling fixed-dimensional analytic scalar factors
through the actual coupled deformation. No analyticity of cutoffs is used. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology ContDiff
set_option maxHeartbeats 1800000

theorem compact_scalar_pair_tube (F : ℂ × ℂ × ℂ → ℂ) (s0 : ℂ) {a b : ℝ}
    (ha : ∀ θ ∈ Icc a b, ∀ φ ∈ Icc a b,
      AnalyticAt ℂ F (s0,limitingAngle θ,limitingAngle φ)) (J : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ θ ∈ Icc a b, ∀ φ ∈ Icc a b,
      ∀ p : ℂ × ℂ × ℂ, ‖p-(s0,limitingAngle θ,limitingAngle φ)‖ ≤ δ →
      AnalyticAt ℂ F p ∧ ∀ k ≤ J, ‖iteratedFDeriv ℝ k F p‖ ≤ C := by
  let K := (fun q : ℝ × ℝ => (s0,limitingAngle q.1,limitingAngle q.2)) '' (Icc a b ×ˢ Icc a b)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by unfold limitingAngle; fun_prop)
  have hF : AnalyticOnNhd ℂ F K := by
    rintro p ⟨⟨θ,φ⟩,⟨hθ,hφ⟩,rfl⟩
    exact ha θ hθ φ hφ
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ F) hF
  obtain ⟨t,C,ht,hC,hjets⟩ := compact_analytic_jet_bounds F hK hF J
  refine ⟨min r t,C,lt_min hr ht,hC,?_⟩
  intro θ hθ φ hφ p hp
  have hbase : (s0,limitingAngle θ,limitingAngle φ) ∈ K := ⟨(θ,φ),⟨hθ,hφ⟩,rfl⟩
  have hFp : AnalyticAt ℂ F p := hsub (mem_cthickening_of_dist_le p _ r K hbase
    (by simpa only [dist_eq_norm] using hp.trans (min_le_left r t)))
  refine ⟨hFp,?_⟩
  intro k hk
  rw [← ((hFp.contDiffAt : ContDiffAt ℂ k F p).restrictScalars_iteratedFDeriv (𝕜 := ℝ)),
    Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars]
  exact (hjets _ hbase p (hp.trans (min_le_right r t)) k hk).1

theorem deformedPoint_boundary_motion {N : ℕ} (hN : 0 < N) (d : LocalBranchData)
    (f : SelectorFunctions) (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1)
    {eps τ lam : ℝ} (heps : 0 ≤ eps) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hlam : 0 ≤ lam)
    (hsmall : d.c₀*eps+2*lam ≤ 1) (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i-limitingAngle (θ i)‖ ≤
      2*(d.c₀*eps+2*lam) := by
  let v := coupledRadialExponent d.c₀ eps τ lam (f.p (θ i)) (f.m (θ i))
    (occupancy (fun l => f.p (θ l))/(N:ℝ))
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hv : |v| ≤ d.c₀*eps+2*lam := by
    have hh := coupledRadialExponent_lambda_bound d.c₀_pos.le heps hτ hlam
      (hf.p_nonneg (θ i)) (hp1 (θ i)) (hf.m_nonneg (θ i)) (hf.m_le_one (θ i))
      (div_nonneg (occupancy_nonneg (fun l => hf.p_nonneg (θ l))) hn.le)
      ((div_le_one hn).mpr (occupancy_le (fun l => hp1 (θ l))))
    exact hh.trans (by nlinarith [mul_le_of_le_one_left hlam hτ1])
  rw [deformedPoint_coupledRadialExponent]
  exact (radialAnglePoint_motion (hv.trans hsmall) _).trans (by linarith)

theorem deformed_pair_positive_jets (f : SelectorFunctions) (hf : RegularSelector f) (J : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N : ℕ, 0 < N → ∀ r τ lam : ℝ,
      0 ≤ r → r ≤ 1 → 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ 1 →
      ∀ i j : Fin N, ∀ p : ℂ × (Fin N → ℝ), ∀ k, 1 ≤ k → k ≤ J →
      ‖iteratedFDeriv ℝ k (fun q : ℂ × (Fin N → ℝ) =>
        (q.1,deformedPoint f r τ lam q.2 i,deformedPoint f r τ lam q.2 j)) p‖ ≤ B := by
  obtain ⟨C,hC,hj⟩ := deformedPoint_joint_finite_jets f hf J
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i j p k hk hkJ
  let S : (ℂ × (Fin N → ℝ)) →L[ℝ] ℂ := ContinuousLinearMap.fst ℝ ℂ (Fin N → ℝ)
  have hS : ‖S‖ ≤ 1 := S.opNorm_le_bound zero_le_one (fun x => by simpa [S] using norm_fst_le x)
  have hy (l : Fin N) : ContDiff ℝ ∞ (fun q : ℂ × (Fin N → ℝ) => deformedPoint f r τ lam q.2 l) :=
    (deformedPoint_fixed_contDiff f r τ lam hf.p_smooth hf.m_smooth l).comp contDiff_snd
  change ‖iteratedFDeriv ℝ k (fun q => (S q,_,_)) p‖ ≤ _
  rw [iteratedFDeriv_prodMk S.contDiff.contDiffAt ((hy i).prodMk (hy j)).contDiffAt
    (by simp : (k:ℕ∞ω) ≤ ∞)]
  apply (multilinear_prod_norm_le_max _ _).trans
  apply max_le ((positive_linear_jet_bound S hS p k hk).trans (le_max_left _ _))
  rw [iteratedFDeriv_prodMk (hy i).contDiffAt (hy j).contDiffAt (by simp : (k:ℕ∞ω) ≤ ∞)]
  exact (multilinear_prod_norm_le_max _ _).trans (max_le
    ((hj N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 i p k hkJ).trans (le_max_right _ _))
    ((hj N hN r τ lam hr hr1 hτ hτ1 hlam hlam1 j p k hkJ).trans (le_max_right _ _)))

theorem actual_compact_scalar_pair_jets (d : LocalBranchData) (f : SelectorFunctions)
    (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) (F : ℂ × ℂ × ℂ → ℂ) {a b : ℝ}
    (hF : ∀ θ ∈ Icc a b, ∀ φ ∈ Icc a b,
      AnalyticAt ℂ F (radialParameter d.theta 0,limitingAngle θ,limitingAngle φ))
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 ≤ eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ,
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, ∀ i j : Fin N, θ i ∈ Icc a b → θ j ∈ Icc a b →
      RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        F (q.1,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam q.2 i,
          deformedPoint f (Real.exp (-d.c₀*eps)) τ lam q.2 j)) (s,θ) J 1 C 0 := by
  obtain ⟨r,A,hr,hA,houter⟩ := compact_scalar_pair_tube F _ hF J
  obtain ⟨B,hB,hinner⟩ := deformed_pair_positive_jets f hf J
  refine ⟨min 1 (r/2),(J.factorial:ℝ)*A*B^J,lt_min zero_lt_one (by positivity),by positivity,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hsmall θ i j hi hj
  let r0 := Real.exp (-d.c₀*eps)
  let g := fun q : ℂ × (Fin N → ℝ) => (q.1,deformedPoint f r0 τ lam q.2 i,deformedPoint f r0 τ lam q.2 j)
  have hr0 : 0 ≤ r0 := (Real.exp_pos _).le
  have hr01 : r0 ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hgs : ContDiff ℝ ∞ g := contDiff_fst.prodMk
    (((deformedPoint_fixed_contDiff f r0 τ lam hf.p_smooth hf.m_smooth i).comp contDiff_snd).prodMk
      ((deformedPoint_fixed_contDiff f r0 τ lam hf.p_smooth hf.m_smooth j).comp contDiff_snd))
  have hb1 := hsmall.trans (min_le_left _ _)
  have hbr := hsmall.trans (min_le_right _ _)
  have hm (l : Fin N) := deformedPoint_boundary_motion hN d f hf hp1 heps hτ hτ1 hlam
    (by linarith [norm_nonneg (s-radialParameter d.theta 0)] : d.c₀*eps+2*lam ≤ 1) θ l
  have hpt : ‖g (s,θ)-(radialParameter d.theta 0,limitingAngle (θ i),limitingAngle (θ j))‖ ≤ r := by
    change max ‖s-radialParameter d.theta 0‖ (max ‖deformedPoint f r0 τ lam θ i-limitingAngle (θ i)‖
      ‖deformedPoint f r0 τ lam θ j-limitingAngle (θ j)‖) ≤ r
    exact max_le (by nlinarith [mul_nonneg d.c₀_pos.le heps])
      (max_le (by have := hm i; nlinarith [norm_nonneg (s-radialParameter d.theta 0)])
        (by have := hm j; nlinarith [norm_nonneg (s-radialParameter d.theta 0)]))
  obtain ⟨ha,hjF⟩ := houter (θ i) hi (θ j) hj (g (s,θ)) hpt
  have hreal : ContDiffAt ℝ ∞ F (g (s,θ)) := (ha.contDiffAt : ContDiffAt ℂ ∞ F _).restrict_scalars ℝ
  refine ⟨hreal.comp (s,θ) hgs.contDiffAt,by positivity,?_⟩
  intro k hk
  simp only [one_zpow,mul_one]
  have hh := real_smooth_composition_jet_bound g F (s,θ) k hgs.contDiffAt hreal A B
    (fun l hl => hjF l (hl.trans hk)) (fun l hl hlk =>
      (hinner N hN r0 τ lam hr0 hr01 hτ hτ1 hlam hlam1 i j (s,θ) l hl (hlk.trans hk)).trans
        (le_self_pow₀ hB (by omega : l ≠ 0)))
  exact hh.trans (by gcongr)

end
end IsingBulk.Tail

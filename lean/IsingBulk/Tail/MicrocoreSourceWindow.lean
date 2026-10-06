import IsingBulk.Tail.MicrocoreVariableJets
import IsingBulk.Tail.MicrocoreParameterSlice
import IsingBulk.Tail.MicrocorePointwiseBudget
import IsingBulk.Tail.MicrocoreLocalDensityJets
import IsingBulk.Tail.MicrocoreDomain
import IsingBulk.Tail.MicrocoreArclength
import IsingBulk.Tail.MicrocorePhaseNeighborhood
import IsingBulk.Tail.MicrocoreWindowGeometry
import IsingBulk.Tail.ScaledCutoffJets
import IsingBulk.Tail.MicrocoreTotalCost
import IsingBulk.Tail.OriginalGlobalDisk

/-! Simultaneous actual-source microcore geometry and all-order coefficient
budget. Every constant precedes H, N, the derivative order and all coordinates. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Filter
open scoped BigOperators Topology

 theorem microcore_source_window_capped (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c E Cφ : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧ 0 < Cφ ∧
    ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+1:ℕ):ℝ) ≤ D*Real.sqrt H →
      let ε := Real.exp (-H)
      let b := microcoreRadius A c (n+1)
      let s := radialParameter d.theta ε
      let v := -d.c₀*ε
      ∀ u : AngularSpace n, (∀ i, |u i| ≤ b) →
        MicrocoreDensityPoint v d.thetaB s u ∧
        (∀ i, ‖originalPhase d ε (u i)‖ ≤ Cφ*Real.sqrt b) ∧
        (∑ i, ‖originalPhase d ε (u i)‖)/4 ≤ ‖1-regularZProduct s (chartMap v d.thetaB s u)‖ ∧
        ∀ j ≤ J,
          ‖((lieStep (microcoreField v d.thetaB))^[j]
            (fun t x => (scaledMicroCutoff (n+1) b x:ℂ)*
              chartPullback v d.thetaB (@microRegularDensity (n+1)) t x)) s u‖ ≤
          Real.exp (E*((n+1:ℕ):ℝ)^2)*‖microcorePhaseFactor (chartMap v d.thetaB s u)‖*
            ∏ i, ‖deriv (originalPhase d ε) (u i)‖ := by
  obtain ⟨A,hA,hgap⟩ := algebraic_microcore_gap d.thetaB halg hnot
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖radialParameter d.theta 0‖ ≠ 0
    rw [IsingBulk.First.radialParameter_norm (by norm_num)]
    norm_num
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hcos : |Real.cos d.thetaB| < 1 := by
    have hs : 0 < Real.sin d.thetaB := d.a_pos
    have hh := Real.sin_sq_add_cos_sq d.thetaB
    rw [abs_lt]
    constructor <;> nlinarith [Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨E₀,rF,hE₀,hrF,hF⟩ := microcore_variable_uniform_exponential_jets s₀ (Real.cos d.thetaB) A hs₀ hS hcos hA.le J
  obtain ⟨C,rA,hC,hrA,hAr⟩ := microcore_regularA_parameter_uniform s₀ (Real.cos d.thetaB) hs₀ hS hcos J
  let r := min rF rA
  have hr : 0 < r := lt_min hrF hrA
  obtain ⟨rP,Cφ,hrP,hCφ,hP⟩ := original_phase_small_radius d r hr
  obtain ⟨rChart,hrChart,hChart⟩ := original_microcore_chart d
  obtain ⟨cGeom,hcGeom,_,hGeom⟩ := original_microcore_window_geometry d
  let c := min (min (rP/2) (rChart/2)) (min cGeom (min cap (1/4)))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcP : c < rP := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hrP)
  have hcChart : c < rChart := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hrChart)
  have hcG : c ≤ cGeom := (min_le_right _ _).trans (min_le_left _ _)
  have hcCap : c ≤ cap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcsmall : c ≤ 1/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨K,hK,hCut⟩ := scaledMicroCutoff_jet_bound J
  obtain ⟨E,hE,hCost⟩ := microcore_total_finite_cost hA.le hc hC hE₀ hK J
  refine ⟨A,c,E,Cφ,hA,hc,hcsmall,hcCap,hE,hCφ,?_⟩
  have hεsmall : ∀ᶠ H : ℝ in atTop, Real.exp (-H) < min r rChart :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (lt_min hr hrChart))
  filter_upwards [hεsmall,microcore_window_epsilon_le_radius D A c hD hA.le hc,
    microcore_window_budget D A d.c₀ c hD hA.le d.c₀_pos hc.le hcsmall,
    hGeom A D hA.le hD] with H hε hεb hBudget hGeometry
  intro n hwindow
  dsimp only
  intro u hu
  let ε := Real.exp (-H)
  let b := microcoreRadius A c (n+1)
  let s := radialParameter d.theta ε
  let v := -d.c₀*ε
  have hN : 1 ≤ n+1 := by omega
  have hb : 0 < b := microcoreRadius_pos A c hc (n+1) hN
  have hbc : b ≤ c := microcoreRadius_le_prefactor A c hA.le hc.le (n+1) hN
  have hεb' : ε ≤ b := hεb (n+1) hN hwindow
  have hchart : MicrocoreJetPoint v d.thetaB s u := hChart ε (Real.exp_pos _) (hε.trans_le (min_le_right _ _))
    n u (fun i => (hu i).trans_lt (hbc.trans_lt hcChart))
  have hphase : ∀ i, ‖originalPhase d ε (u i)‖ ≤ Cφ*Real.sqrt b ∧ ‖originalPhase d ε (u i)‖ < r :=
    fun i => hP ε b (u i) (Real.exp_pos _) hεb' (hbc.trans_lt hcP) (hu i)
  have hφ : ∀ i, ‖chartMap v d.thetaB s u i‖ < r := by
    intro i
    rw [original_chartMap_eq]
    exact (hphase i).2
  have hs : ‖s-s₀‖ < r := by
    rw [radialParameter_sub_zero_norm d.theta ε (Real.exp_pos _).le]
    exact hε.trans_le (min_le_left _ _)
  have hYgap : Real.exp (-A*(n+1:ℕ))/2 ≤ ‖1-regularYProduct s (chartMap v d.thetaB s u)‖ := by
    rw [original_regularYProduct_eq d ε u hchart.g_pos]
    exact hgap (n+1) hN u d.c₀ ε b d.c₀_pos.le (Real.exp_pos _).le hu (hBudget (n+1) hN hwindow)
  have hfj := hF (n+1) hN s (chartMap v d.thetaB s u)
    (hs.trans_le (min_le_left _ _)) (fun i => (hφ i).trans_le (min_le_left _ _)) hYgap
  have hAj := fun i => hAr s (chartMap v d.thetaB s u i)
    (hs.trans_le (min_le_right _ _)) ((hφ i).trans_le (min_le_right _ _))
  have hgeometry := hGeometry (n+1) hN hwindow u (fun i =>
    (hu i).trans (microcoreRadius_mono_prefactor A c cGeom hcG (n+1)))
  have hZgap : (∑ i, ‖originalPhase d ε (u i)‖)/4 ≤ ‖1-regularZProduct s (chartMap v d.thetaB s u)‖ := by
    rw [original_chartMap_eq]
    exact hgeometry.2.2
  have hsumpos : 0 < ∑ i, ‖originalPhase d ε (u i)‖ := by
    apply Finset.sum_pos
    · intro i _
      apply norm_pos_iff.mpr
      intro hz
      have hreal : 0 < (originalPhase d ε (u i)).re := (hgeometry.1 i).1
      rw [hz] at hreal
      simp at hreal
    · exact Finset.univ_nonempty
  have hZne : 1-regularZProduct s (chartMap v d.thetaB s u) ≠ 0 := norm_pos_iff.mp
    ((div_pos hsumpos (by norm_num)).trans_le hZgap)
  refine ⟨⟨hchart,hfj.1,hZne⟩,fun i => (hphase i).1,hZgap,?_⟩
  intro j hj
  rw [microcore_density_point_all_order v d.thetaB s u _ (scaledMicroCutoff_smooth _ _) hchart hfj.1 hZne j,norm_mul]
  have hW : 0 ≤ K^(n+1)*(b⁻¹)^J := by positivity
  have hterms := microcoreTermSum_norm_bound v d.thetaB (scaledMicroCutoff (n+1) b)
    microcoreVariableFactor s u J j hj C (Real.exp (E₀*((n+1:ℕ):ℝ)^2))
    (K^(n+1)*(b⁻¹)^J) hC hW hfj.1 hchart.regularA_analytic hfj.2 hAj
    (fun l hl => hCut (n+1) b hb (by linarith) l (hl.trans hj) u)
  have hcost : (n+2:ℝ)^j*(K^(n+1)*(b⁻¹)^J)*
      ((2^J*C)^j*Real.exp (E₀*((n+1:ℕ):ℝ)^2)) ≤ Real.exp (E*((n+1:ℕ):ℝ)^2) := by
    have hBase : 1 ≤ (2:ℝ)^J*C := by
      have hp : 1 ≤ (2:ℝ)^J := one_le_pow₀ (by norm_num)
      nlinarith
    have hpN : (n+2:ℝ)^j ≤ (n+2:ℝ)^J := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n+2 by omega)) hj
    have hpC : (2^J*C)^j ≤ (2^J*C)^J := pow_le_pow_right₀ hBase hj
    have hh := hCost (n+1) hN J le_rfl
    have he : ((n+1:ℕ):ℝ)+1=(n+2:ℝ) := by push_cast; ring
    rw [he] at hh
    apply le_trans _ hh
    dsimp [b]
    calc
      _ ≤ (n+2:ℝ)^J*(K^(n+1)*(microcoreRadius A c (n+1))⁻¹^J)*
          ((2^J*C)^J*Real.exp (E₀*((n+1:ℕ):ℝ)^2)) := by gcongr
      _ = _ := by ring
  have hterms' := hterms.trans (mul_le_mul_of_nonneg_left hcost (norm_nonneg _))
  rw [original_chartJacobian_norm d ε u
    (fun i => by simpa only [s,v,original_chartW_eq] using hchart.re_pos i)
    (fun i => by simpa only [s,v,original_chartW_eq] using hchart.im_pos i)] at hterms'
  have hh := mul_le_mul_of_nonneg_left hterms' (norm_nonneg (microcorePhaseFactor (chartMap v d.thetaB s u)))
  nlinarith

end
end IsingBulk.Tail

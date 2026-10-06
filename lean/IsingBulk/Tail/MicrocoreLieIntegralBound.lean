import IsingBulk.Tail.MicrocoreSourceWindow
import IsingBulk.Tail.MicrocorePhaseMajorant
import IsingBulk.Tail.MicrocoreBranchProduct

/-! Integration of the actual microcore Lie density against the original
branch arclength. The derivative-under-integral identity is attached separately. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Filter Set
open scoped BigOperators Topology

def originalMicrocoreLieDensity {n : ℕ} (d : LocalBranchData) (ε b : ℝ) (j : ℕ)
    (s : ℂ) (u : AngularSpace n) : ℂ :=
  ((lieStep (microcoreField (-d.c₀*ε) d.thetaB))^[j]
    (fun t x => (scaledMicroCutoff (n+1) b x:ℂ)*
      chartPullback (-d.c₀*ε) d.thetaB (@microRegularDensity (n+1)) t x)) s u

def microcoreCoreMeasure (N : ℕ) (b : ℝ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Icc (-b) b))

theorem microcore_source_lie_integral_bound (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧
    ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
      let ε := Real.exp (-H)
      let b := microcoreRadius A c (n+2)
      (∀ u : Fin (n+2) → ℝ, (∀ i, |u i| ≤ b) →
        MicrocoreDensityPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) ∧
      ∀ j ≤ J,
        ‖∫ u : Fin (n+2) → ℝ, originalMicrocoreLieDensity d ε b j (radialParameter d.theta ε) u
          ∂microcoreCoreMeasure (n+2) b‖ ≤
          Real.exp (E*((n+2:ℕ):ℝ)^2)*(Real.sqrt b)^((n+2)^2-1) := by
  obtain ⟨K,rL,hK,hrL,hLaplace⟩ := original_branch_product_laplace_bound d
  obtain ⟨A,c,E₀,Cφ,hA,hc,hcsmall,hcCap,hE₀,hCφ,hWindow⟩ :=
    microcore_source_window_capped d halg hnot (min cap (rL/2)) (by positivity) J D hD
  obtain ⟨E,hE,hCost⟩ := microcore_integral_prefactor E₀ Cφ K hE₀ hCφ hK
  refine ⟨A,c,E,hA,hc,hcsmall,hcCap.trans (min_le_left _ _),hE,?_⟩
  have hεsmall : ∀ᶠ H : ℝ in atTop, Real.exp (-H) < rL :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hrL)
  filter_upwards [hWindow,hεsmall] with H hH hεr
  intro n hwindow
  dsimp only
  constructor
  · intro u hu
    exact (hH (n+1) hwindow u hu).1
  ·
    intro j hj
    let N := n+2
    let ε := Real.exp (-H)
    let b := microcoreRadius A c N
    let s := radialParameter d.theta ε
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hb : 0 < b := microcoreRadius_pos A c hc N hN
    have hbr : b < rL := (microcoreRadius_le_prefactor A c hA.le hc.le N hN).trans_lt
      ((hcCap.trans (min_le_right _ _)).trans_lt (half_lt_self hrL))
    obtain ⟨hInt,hLb⟩ := hLaplace n ε b (Real.exp_pos _) hεr hb hbr
    let f : (Fin N → ℝ) → ℝ := fun u =>
      (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/(∑ i, ‖originalPhase d ε (u i)‖)
    let B := 4*Real.exp (E₀*(N:ℝ)^2)*(2*Cφ*Real.sqrt b)^(N*(N-1))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hpoint : ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ b) →
        ‖originalMicrocoreLieDensity d ε b j s u‖ ≤ B*f u := by
      intro u hu
      obtain ⟨hdata,hphase,hZ,hbound⟩ := hH (n+1) hwindow u hu
      have hchart := hdata.1
      let φ : Fin N → ℂ := fun i => originalPhase d ε (u i)
      have hsum : 0 < ∑ i, ‖φ i‖ := by
        apply Finset.sum_pos
        · intro i _
          have hr : 0 < (originalW d ε (u i)).re := by
            simpa only [original_chartW_eq] using hchart.re_pos i
          have hi : 0 < (originalW d ε (u i)).im := by
            simpa only [original_chartW_eq] using hchart.im_pos i
          have hφpos : 0 < (φ i).re := (lowerArccos_sheet _ hr hi).2.1
          apply norm_pos_iff.mpr
          intro hz
          rw [hz] at hφpos
          simp at hφpos
        · exact Finset.univ_nonempty
      have hQ := microcore_phase_factor_norm_bound φ (Cφ*Real.sqrt b) (by positivity) hphase hsum
        (by simpa only [original_chartMap_eq,regularZProduct,φ,ε] using hZ)
      have hsource := hbound j hj
      rw [original_chartMap_eq] at hsource
      have hp : 0 ≤ ∏ i, ‖deriv (originalPhase d ε) (u i)‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ (Real.exp_pos (E₀*(N:ℝ)^2)).le) hp
      apply hsource.trans (hh.trans_eq ?_)
      dsimp [B,f,φ]
      ring
    have hae : ∀ᵐ u ∂microcoreCoreMeasure N b, (∀ i, |u i| ≤ b) := by
      have hh : ∀ i : Fin N, ∀ᵐ u ∂microcoreCoreMeasure N b, u i ∈ Icc (-b) b := fun i =>
        (Measure.tendsto_eval_ae_ae (i := i)) (ae_restrict_mem measurableSet_Icc)
      filter_upwards [ae_all_iff.mpr hh] with u hu
      exact fun i => abs_le.mpr (hu i)
    have hmajor : Integrable (fun u : Fin N → ℝ => B*f u) (microcoreCoreMeasure N b) := hInt.const_mul B
    have hint := norm_integral_le_of_norm_le hmajor (hae.mono (fun u hu => hpoint u hu))
    rw [integral_const_mul] at hint
    have hL := mul_le_mul_of_nonneg_left hLb hB
    have he : B*(2*K^N*(Real.sqrt b)^(n+1)) =
        (8*Real.exp (E₀*(N:ℝ)^2)*(2*Cφ)^(N*(N-1))*K^N)*(Real.sqrt b)^(N^2-1) := by
      have hd : N*(N-1)+(n+1)=N^2-1 := by
        dsimp [N]
        have hh : (n+2)*(n+1)+(n+1)+1=(n+2)^2 := by ring
        omega
      dsimp [B]
      rw [mul_pow,← hd,pow_add]
      ring
    rw [he] at hL
    have hcost := mul_le_mul_of_nonneg_right (hCost N hN)
      (pow_nonneg (Real.sqrt_nonneg b) (N^2-1))
    exact hint.trans (hL.trans hcost)

end
end IsingBulk.Tail

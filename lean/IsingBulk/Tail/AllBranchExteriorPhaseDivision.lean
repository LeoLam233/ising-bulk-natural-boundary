import IsingBulk.Tail.LocalSmoothDivision
import IsingBulk.Tail.MicrocoreComplexChart

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology ContDiff
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def allBranchPairPhaseDifference (v θ : ℝ) (z : (ℝ × ℝ) × ℂ) : ℂ :=
  chartPhase z.2 v θ (z.1.1:ℂ)-chartPhase z.2 v θ (z.1.2:ℂ)

def allBranchPairPhaseEmbedding (z : (ℝ × ℝ) × ℂ) : ℂ × ℂ × ℂ :=
  (z.2,(z.1.1:ℂ),(z.1.2:ℂ))

theorem allBranchPairPhaseEmbedding_smooth : ContDiff ℝ ∞ allBranchPairPhaseEmbedding := by
  exact contDiff_snd.prodMk ((Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)).prodMk
    (Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_fst)))

theorem allBranchExterior_pair_phase_analytic (v θ : ℝ) (z : ℂ × ℂ × ℂ)
    (hs : z.1 ≠ 0)
    (hr₁ : 0 < (chartW z.1 v θ z.2.1).re) (hi₁ : 0 < (chartW z.1 v θ z.2.1).im)
    (hr₂ : 0 < (chartW z.1 v θ z.2.2).re) (hi₂ : 0 < (chartW z.1 v θ z.2.2).im) :
    AnalyticAt ℂ (fun y : ℂ × ℂ × ℂ => chartPhase y.1 v θ y.2.1-chartPhase y.1 v θ y.2.2) z := by
  have hy₁ : AnalyticAt ℂ (fun y : ℂ × ℂ × ℂ => angularY v θ y.2.1) z := by
    unfold angularY
    fun_prop
  have hy₂ : AnalyticAt ℂ (fun y : ℂ × ℂ × ℂ => angularY v θ y.2.2) z := by
    unfold angularY
    fun_prop
  have hw₁ : AnalyticAt ℂ (fun y : ℂ × ℂ × ℂ => chartW y.1 v θ y.2.1) z :=
    (analyticAt_fst.add (analyticAt_fst.inv hs)).sub
      ((hy₁.add (hy₁.inv (Complex.exp_ne_zero _))).div_const)
  have hw₂ : AnalyticAt ℂ (fun y : ℂ × ℂ × ℂ => chartW y.1 v θ y.2.2) z :=
    (analyticAt_fst.add (analyticAt_fst.inv hs)).sub
      ((hy₂.add (hy₂.inv (Complex.exp_ne_zero _))).div_const)
  exact ((lowerArccos_analytic_upper_quadrant _ hr₁ hi₁).comp
    (f := fun y : ℂ × ℂ × ℂ => chartW y.1 v θ y.2.1) hw₁).sub
    ((lowerArccos_analytic_upper_quadrant _ hr₂ hi₂).comp
      (f := fun y : ℂ × ℂ × ℂ => chartW y.1 v θ y.2.2) hw₂)

theorem allBranchExterior_phase_division_germ (v θ : ℝ) (z : (ℝ × ℝ) × ℂ)
    (hs : z.2 ≠ 0)
    (hr₁ : 0 < (chartW z.2 v θ (z.1.1:ℂ)).re) (hi₁ : 0 < (chartW z.2 v θ (z.1.1:ℂ)).im)
    (hr₂ : 0 < (chartW z.2 v θ (z.1.2:ℂ)).re) (hi₂ : 0 < (chartW z.2 v θ (z.1.2:ℂ)).im) :
    ∃ C : (ℝ × ℝ) × ℂ → ℂ, ContDiffAt ℝ ∞ C z ∧
      ∀ᶠ y in 𝓝 z, allBranchPairPhaseDifference v θ y=(y.1.1-y.1.2:ℝ) • C y := by
  let G : ℂ × ℂ × ℂ → ℂ := fun y => chartPhase y.1 v θ y.2.1-chartPhase y.1 v θ y.2.2
  have hG := allBranchExterior_pair_phase_analytic v θ (allBranchPairPhaseEmbedding z) hs hr₁ hi₁ hr₂ hi₂
  have he : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ (allBranchPairPhaseDifference v θ) y := by
    have hp := allBranchPairPhaseEmbedding_smooth.continuous.continuousAt.tendsto.eventually hG.eventually_analyticAt
    filter_upwards [hp] with y hy
    have hh := (hy.contDiffAt.restrict_scalars ℝ).comp y allBranchPairPhaseEmbedding_smooth.contDiffAt
    exact hh
  obtain ⟨U,hU,hopen,hz⟩ := eventually_nhds_iff.mp he
  exact smooth_hadamard_division_near (allBranchPairPhaseDifference v θ) hopen hU
    (fun y p _ => sub_self _) hz

theorem allBranchExterior_phase_quotient_diagonal (v θ u : ℝ) (s : ℂ)
    (hr : 0 < (chartW s v θ (u:ℂ)).re) (hi : 0 < (chartW s v θ (u:ℂ)).im)
    (C : (ℝ × ℝ) × ℂ → ℂ) (hC : ContDiffAt ℝ ∞ C ((u,u),s))
    (he : ∀ᶠ y in 𝓝 ((u,u),s), allBranchPairPhaseDifference v θ y=(y.1.1-y.1.2:ℝ) • C y) :
    C ((u,u),s)=chartB s v θ (u:ℂ) := by
  have hpath : HasDerivAt (fun x : ℝ => ((x,u),s)) ((1,0),0) u :=
    ((hasDerivAt_id u).prodMk (hasDerivAt_const u u)).prodMk (hasDerivAt_const u s)
  have hCx := (hC.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt u hpath
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).sub_const u)
  have hright := hlin.mul hCx
  have hright' : HasDerivAt (fun x : ℝ => ((x-u:ℝ):ℂ)*C ((x,u),s)) (C ((u,u),s)) u := by
    convert! hright using 1; simp
  have hleft := (chartPhase_real_angular s v θ u hr hi).sub_const (chartPhase s v θ (u:ℂ))
  have he' := hpath.continuousAt.tendsto.eventually he
  have hder : HasDerivAt (fun x : ℝ => chartPhase s v θ (x:ℂ)-chartPhase s v θ (u:ℂ))
      (C ((u,u),s)) u := hright'.congr_of_eventuallyEq he'
  exact hder.unique hleft

theorem allBranchExterior_phase_division_nonzero (v θ u : ℝ) (s : ℂ)
    (hs : s ≠ 0) (hr : 0 < (chartW s v θ (u:ℂ)).re) (hi : 0 < (chartW s v θ (u:ℂ)).im)
    (hg : angularG v θ (u:ℂ) ≠ 0) (hsi : Complex.sin (chartPhase s v θ (u:ℂ)) ≠ 0) :
    ∃ C : (ℝ × ℝ) × ℂ → ℂ, ContDiffAt ℝ ∞ C ((u,u),s) ∧ C ((u,u),s) ≠ 0 ∧
      ∀ᶠ y in 𝓝 ((u,u),s), allBranchPairPhaseDifference v θ y=(y.1.1-y.1.2:ℝ) • C y := by
  obtain ⟨C,hC,he⟩ := allBranchExterior_phase_division_germ v θ ((u,u),s) hs hr hi hr hi
  refine ⟨C,hC,?_,he⟩
  rw [allBranchExterior_phase_quotient_diagonal v θ u s hr hi C hC he]
  exact div_ne_zero hg hsi

end
end IsingBulk.Tail

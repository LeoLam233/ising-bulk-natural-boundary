import IsingBulk.Preferred22.WeightedIntegralAnalytic
import IsingBulk.Preferred22.RadialLogImprovement

/-! Exact complex derivatives of the actual complete coefficient partition.
This is separate from the still-required equality between a differentiated
piece integral and its recursively transported density integral. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

lemma preferred_radial_iterated_hasDerivAt {F : ℂ → ℂ} (ζ : ℂ) (ε : ℝ) (j : ℕ)
    (hF : AnalyticAt ℂ F ((1+(ε:ℂ))*ζ)) :
    HasDerivAt (fun t : ℝ => iteratedDeriv j F ((1+(t:ℂ))*ζ))
      (ζ*iteratedDeriv (j+1) F ((1+(ε:ℂ))*ζ)) ε := by
  have hd := (IsingBulk.First.analyticAt_iteratedDeriv hF j).differentiableAt.hasDerivAt
  have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (ε:ℂ) := by
    simpa using ((hasDerivAt_id (ε:ℂ)).const_add 1).mul_const ζ
  convert! (hd.comp (ε:ℂ) hp).comp_ofReal using 1
  simp only [iteratedDeriv_succ,mul_comm]

/-- Equality along an open real radial path implies equality of every
complex derivative when both actual functions are analytic there. -/
theorem preferred_radial_iteratedDeriv_congr {F G : ℂ → ℂ} {ζ : ℂ} (hζ : ζ≠0)
    (hF : ∀ ε : ℝ, 0<ε → AnalyticAt ℂ F ((1+(ε:ℂ))*ζ))
    (hG : ∀ ε : ℝ, 0<ε → AnalyticAt ℂ G ((1+(ε:ℂ))*ζ))
    (hFG : ∀ ε : ℝ, 0<ε → F ((1+(ε:ℂ))*ζ)=G ((1+(ε:ℂ))*ζ)) :
    ∀ j : ℕ, ∀ ε : ℝ, 0<ε →
      iteratedDeriv j F ((1+(ε:ℂ))*ζ)=iteratedDeriv j G ((1+(ε:ℂ))*ζ) := by
  intro j
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hFG
  | succ j ih =>
    intro ε hε
    have he : (fun t : ℝ => iteratedDeriv j F ((1+(t:ℂ))*ζ))=ᶠ[𝓝 ε]
        (fun t : ℝ => iteratedDeriv j G ((1+(t:ℂ))*ζ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hε] with t ht
      exact ih t ht
    have hf := preferred_radial_iterated_hasDerivAt ζ ε j (hF ε hε)
    have hg := preferred_radial_iterated_hasDerivAt ζ ε j (hG ε hε)
    apply mul_left_cancel₀ hζ
    exact hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)

/-- Every complex derivative of the literal complete coefficient equals
those of the selected population, full right integral and every named
anchor. This has no tail or integrated-transport premise. -/
theorem preferred_complete_derivative_partition (n : ℕ) (he : Even (n+1))
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (hrp : Function.Periodic r (2*Real.pi))
    (j : ℕ) {ε : ℝ} (hε : 0<ε) :
    iteratedDeriv j (coefficient (n+1)) (IsingBulk.Branch.radialParameter d.alpha ε)=
      iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m)
        (IsingBulk.Branch.radialParameter d.alpha ε)+
      2*(iteratedDeriv j (preferredTransportedIntegral (n := n) .right B.delta τ
          preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)+
        ∑ a : Fin (n+1), iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ
          preferredPopulationCutoff B.p B.m r 0) (IsingBulk.Branch.radialParameter d.alpha ε)) := by
  let F := preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m
  let R := preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m r 0
  let A := fun a : Fin (n+1) => preferredTransportedIntegral (.anchor a) B.delta τ
    preferredPopulationCutoff B.p B.m r 0
  let G := fun s : ℂ => F s+2*(R s+∑ a,A a s)
  have hF (t : ℝ) (ht : 0<t) : AnalyticAt ℂ F (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredFullPopulationIntegral_analyticAt n d B hτ preferredPopulationCutoff
      preferredPopulationCutoff_smooth.continuous (preferredRadialTrace_im_pos d ht)
  have hR (t : ℝ) (ht : 0<t) : AnalyticAt ℂ R (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredTransportedIntegral_zero_analyticAt n d B .right hτ preferredPopulationCutoff r
      preferredPopulationCutoff_smooth hr hrp (preferredRadialTrace_im_pos d ht)
  have hA (t : ℝ) (ht : 0<t) (a : Fin (n+1)) :
      AnalyticAt ℂ (A a) (IsingBulk.Branch.radialParameter d.alpha t) :=
    preferredTransportedIntegral_zero_analyticAt n d B (.anchor a) hτ preferredPopulationCutoff r
      preferredPopulationCutoff_smooth hr hrp (preferredRadialTrace_im_pos d ht)
  have hAs (t : ℝ) (ht : 0<t) :
      AnalyticAt ℂ (fun s => ∑ a,A a s) (IsingBulk.Branch.radialParameter d.alpha t) :=
    Finset.univ.analyticAt_fun_sum (fun a _ => hA t ht a)
  have hG (t : ℝ) (ht : 0<t) : AnalyticAt ℂ G (IsingBulk.Branch.radialParameter d.alpha t) :=
    (hF t ht).add (analyticAt_const.mul ((hR t ht).add (hAs t ht)))
  have hcoef (t : ℝ) (ht : 0<t) :
      AnalyticAt ℂ (coefficient (n+1)) (IsingBulk.Branch.radialParameter d.alpha t) := by
    apply coefficient_analyticAt
    simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one]
      using radialPath_exterior (Complex.norm_exp_ofReal_mul_I d.alpha) ht
  have heq : iteratedDeriv j (coefficient (n+1)) (IsingBulk.Branch.radialParameter d.alpha ε)=
      iteratedDeriv j G (IsingBulk.Branch.radialParameter d.alpha ε) := by
    have hc' : ∀ t : ℝ, 0<t →
        AnalyticAt ℂ (coefficient (n+1)) ((1+(t:ℂ))*Complex.exp ((d.alpha:ℂ)*Complex.I)) := by
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one]
        using hcoef
    have hg' : ∀ t : ℝ, 0<t →
        AnalyticAt ℂ G ((1+(t:ℂ))*Complex.exp ((d.alpha:ℂ)*Complex.I)) := by
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one]
        using hG
    have he' : ∀ t : ℝ, 0<t →
        coefficient (n+1) ((1+(t:ℂ))*Complex.exp ((d.alpha:ℂ)*Complex.I)) =
        G ((1+(t:ℂ))*Complex.exp ((d.alpha:ℂ)*Complex.I)) := by
      intro t ht
      simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one,G,F,R,A]
        using preferred_complete_transport_partition n he d B ht hτ r hr hrp
    simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one]
      using preferred_radial_iteratedDeriv_congr (Complex.exp_ne_zero _) hc' hg' he' j ε hε
  rw [heq]
  change iteratedDeriv j (fun s => F s+2*(R s+∑ a,A a s)) _ = _
  have hsecond : AnalyticAt ℂ (fun s => (2:ℂ)*(R s+∑ a,A a s))
      (IsingBulk.Branch.radialParameter d.alpha ε) :=
    analyticAt_const.mul ((hR ε hε).add (hAs ε hε))
  rw [iteratedDeriv_fun_add (hF ε hε).contDiffAt hsecond.contDiffAt,
    iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add (hR ε hε).contDiffAt (hAs ε hε).contDiffAt,
    iteratedDeriv_fun_sum (fun a _ => (hA ε hε a).contDiffAt)]

end
end IsingBulk.Preferred22

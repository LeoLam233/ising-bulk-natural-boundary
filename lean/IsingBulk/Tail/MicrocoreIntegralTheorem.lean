import IsingBulk.Tail.MicrocoreStageRegularity
import IsingBulk.Tail.MicrocoreDomain

/-! Actual compact microcore Lie integral identity. The source center chart
constructs its own common parameter neighborhood; no zero-flux or derivative
identity is accepted as data. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie MeasureTheory Filter Set Function
open scoped Topology ContDiff

def microcoreLieDensity {n : ℕ} (v theta : ℝ) (w : AngularSpace n → ℝ) (j : ℕ) :=
  (lieStep (microcoreField v theta))^[j]
    (fun s x => (w x:ℂ)*chartPullback v theta (@microRegularDensity (n+1)) s x)

theorem microcoreLieDensity_joint_regular {n : ℕ} (v theta : ℝ)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w) (j : ℕ) (s : ℂ) (x : AngularSpace n)
    (hp : MicrocoreDensityPoint v theta s x) :
    ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n => microcoreLieDensity v theta w j z.1 z.2) (s,x) ∧
    ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n =>
      deriv (fun t => microcoreLieDensity v theta w j t z.2) z.1) (s,x) := by
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun z => microRegularDensity z.1 z.2
  have hF : AnalyticAt ℂ F (s,chartMap v theta s x) :=
    microRegularDensity_analytic _ hp.2.1 hp.2.2
  have hreg := microcoreTermSum_joint_regular v theta w hw F j s x hp.1 hF
  have hpoint := microcoreDensityPoint_eventually v theta s x hp
  have heq : (fun z : ℂ × AngularSpace n => microcoreLieDensity v theta w j z.1 z.2) =ᶠ[𝓝 (s,x)]
      (fun z => microcoreTermSum v theta w F j z.1 z.2) := by
    filter_upwards [hpoint] with z hz
    exact microcore_full_density_point_all_order v theta z.1 z.2 w hw hz j
  refine ⟨hreg.1.congr_of_eventuallyEq heq,?_⟩
  apply hreg.2.congr_of_eventuallyEq
  filter_upwards [hpoint] with z hz
  have hzpoint := microcoreDensityPoint_eventually v theta z.1 z.2 hz
  have he : (fun t => microcoreLieDensity v theta w j t z.2) =ᶠ[𝓝 z.1]
      (fun t => microcoreTermSum v theta w F j t z.2) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hzpoint] with t ht
    exact microcore_full_density_point_all_order v theta t z.2 w hw ht j
  exact he.deriv_eq

theorem contDiff_of_closed_support {n : ℕ} {K : Set (AngularSpace n)}
    (f : AngularSpace n → ℂ) (hsupp : tsupport f ⊆ K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ K
  · exact hf x hx
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsupp h)))

theorem microcoreField_spatial_contDiffAt {n : ℕ} (v theta : ℝ) (s : ℂ)
    (x : AngularSpace n) (hp : MicrocoreJetPoint v theta s x) (i : Fin (n+1)) :
    ContDiffAt ℝ ∞ (fun y => microcoreField v theta s y i) x := by
  have hg : AnalyticAt ℂ (angularG v theta) (x i:ℂ) := by
    have hy : AnalyticAt ℂ (angularY v theta) (x i:ℂ) :=
      (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul analyticAt_const)).cexp
    exact (analyticAt_const.mul (hy.sub (hy.inv (Complex.exp_ne_zero _)))).div_const
  have hn : angularG v theta (x i) ≠ 0 := by
    intro hz
    simpa [hz] using hp.g_pos i
  have ha : AnalyticAt ℂ (fun u : ℂ => chartA s v theta u) (x i:ℂ) :=
    analyticAt_const.div hg.neg (neg_ne_zero.mpr hn)
  have hc : ContDiffAt ℝ ∞ (fun u : ℂ => chartA s v theta u) (x i:ℂ) :=
    ha.contDiffAt.restrict_scalars ℝ
  exact hc.comp x (Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (contDiff_apply ℝ ℝ i).contDiffAt)

theorem microcore_compact_integral_iteratedDeriv {n : ℕ} (v theta : ℝ)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    {K : Set (AngularSpace n)} (hK : IsCompact K) (hsupp : tsupport w ⊆ K)
    {s : ℂ} (hpoint : ∀ x ∈ K, MicrocoreDensityPoint v theta s x) (j : ℕ) :
    iteratedDeriv j (fun t => ∫ x, (w x:ℂ)*
      chartPullback v theta (@microRegularDensity (n+1)) t x) s =
      ∫ x, microcoreLieDensity v theta w j s x := by
  obtain ⟨U,hU,hs,hdom⟩ := microcore_compact_parameter_domain v theta s K hK hpoint
  let A : ℂ → AngularSpace n → ℂ := fun t x => (w x:ℂ)*
    chartPullback v theta (@microRegularDensity (n+1)) t x
  have hsA : ∀ t ∈ U, support (A t) ⊆ K := by
    intro t ht x hx
    have hwx : w x ≠ 0 := by
      intro hz
      simp [A,hz] at hx
    exact hsupp (subset_closure hwx)
  have hsiter (k : ℕ) (t : ℂ) (ht : t ∈ U) :
      tsupport (microcoreLieDensity v theta w k t) ⊆ K :=
    iterate_lieStep_support_subset _ A hU hK.isClosed hsA k t ht
  have hreg (k : ℕ) (t : ℂ) (ht : t ∈ U) (x : AngularSpace n) (hx : x ∈ K) :=
    microcoreLieDensity_joint_regular v theta w hw k t x (hdom t ht x hx)
  have hflux (k : ℕ) (t : ℂ) (ht : t ∈ U) (i : Fin (n+1)) :
      ContDiff ℝ 1 (fun x => microcoreField v theta t x i*microcoreLieDensity v theta w k t x) := by
    have hsupport : tsupport (fun x => microcoreField v theta t x i*microcoreLieDensity v theta w k t x) ⊆ K := by
      apply (closure_mono (show support (fun x => microcoreField v theta t x i*microcoreLieDensity v theta w k t x) ⊆
        support (microcoreLieDensity v theta w k t) from fun x hx => (mul_ne_zero_iff.mp hx).2)).trans
      exact hsiter k t ht
    apply (contDiff_of_closed_support _ hsupport _).of_le (by simp)
    intro x hx
    exact (microcoreField_spatial_contDiffAt v theta t x (hdom t ht x hx).1 i).mul
      ((hreg k t ht x hx).1.comp x (contDiffAt_const.prodMk contDiffAt_id))
  have hid := compact_support_iterate_lieStep_integral_on hK hU (microcoreField v theta) A j
    (fun k hk t ht => subset_closure.trans (hsiter k t ht))
    (fun k hk p hp => (hreg k p.1 hp.1 p.2 hp.2).1.continuousAt.continuousWithinAt)
    (fun k hk p hp => (hreg k p.1 hp.1 p.2 hp.2).2.continuousAt.continuousWithinAt)
    ?_ (fun k hk t ht i => hflux k t ht i)
  · simpa only [iteratedDeriv_eq_iterate,A,microcoreLieDensity] using (hid hs).symm
  · intro k hk t ht x hx
    have hp := hdom t ht x hx
    have he : (fun z => microcoreLieDensity v theta w k z x) =ᶠ[𝓝 t]
        (fun z => microcoreTermSum v theta w
          (fun q : ℂ × (Fin (n+1) → ℂ) => microRegularDensity q.1 q.2) k z x) := by
      filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually
        (microcoreDensityPoint_eventually v theta t x hp)] with z hz
      exact microcore_full_density_point_all_order v theta z x w hw hz k
    apply DifferentiableAt.congr_of_eventuallyEq _ he
    apply (list_parameter_deriv_sum _ _ t _).1
    intro T hT
    have hTa := microcoreJetTerms_analytic _ k _ (microRegularDensity_analytic _ hp.2.1 hp.2.2)
      hp.1.regularA_analytic T hT
    exact (T.source_differentiable v theta t x w hw hp.1.s_ne hp.1.re_pos hp.1.im_pos hp.1.sin_ne hTa).1

end
end IsingBulk.Tail

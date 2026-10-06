import IsingBulk.Tail.SelectorIntegration
import IsingBulk.First.CompactParameterIntegral

/-! Periodic-box Lie transport. The spatial integral vanishes by actual
periodic face equality; no flux-exhaustion or integral-transport premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology ContDiff BigOperators

lemma periodic_C1_divergence_integrable_zero {n : ℕ}
    (F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    (hF : ∀ i, ContDiff ℝ 1 (fun x => F x i))
    (hp : ∀ i, CoordinatePeriodic (n+1) (fun x => F x i)) :
    IntegrableOn (IsingBulk.Lie.divergence F) (angleBox (n+1)) ∧
      (∫ x in angleBox (n+1), IsingBulk.Lie.divergence F x)=0 := by
  have hc : Continuous (IsingBulk.Lie.divergence F) := by
    unfold IsingBulk.Lie.divergence
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi : IntegrableOn (IsingBulk.Lie.divergence F) (angleBox (n+1)) volume :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc : IsCompact (angleBox (n+1)))
  refine ⟨hi,?_⟩
  unfold angleBox
  rw [IsingBulk.Lie.integral_divergence_eq_flux (fun _ => 0) (fun _ => 2*Real.pi)
    (fun _ => Real.two_pi_pos.le) F
    (fun i => (hF i).continuous.continuousOn)
    (fun x _ i => (hF i).differentiable (by norm_num) x) hi,
    IsingBulk.Lie.periodic_boundaryFlux_zero _ _ F
      (fun i x => coordinatePeriodic_faces (hp i) i x)]

 theorem periodic_sector_lie_step {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hc : ContinuousOn (fun p : ℂ × AngularSpace n => A p.1 p.2) (U ×ˢ angleBox (n+1)))
    (hdc : ContinuousOn (fun p : ℂ × AngularSpace n => deriv (fun t => A t p.2) p.1)
      (U ×ˢ angleBox (n+1)))
    (hd : ∀ s ∈ U, ∀ x ∈ angleBox (n+1), DifferentiableAt ℂ (fun t => A t x) s)
    (hflux : ∀ s ∈ U, ∀ i, ContDiff ℝ 1 (fun x => V s x i*A s x))
    (hperiod : ∀ s ∈ U, ∀ i, CoordinatePeriodic (n+1) (fun x => V s x i*A s x))
    {s : ℂ} (hs : s ∈ U) :
    IntegrableOn (fun x => lieStep V A s x) (angleBox (n+1)) ∧
      HasDerivAt (fun t => ∫ x in angleBox (n+1), A t x)
        (∫ x in angleBox (n+1), lieStep V A s x) s := by
  have hder := IsingBulk.First.hasDerivAt_compact_integral (μ := volume)
    (isCompact_Icc : IsCompact (angleBox (n+1))) (hU.mem_nhds hs)
    A (fun s x => deriv (fun t => A t x) s) hc hdc
    (fun t ht x hx => (hd t ht x hx).hasDerivAt)
  have hdi : IntegrableOn (fun x => deriv (fun t => A t x) s) (angleBox (n+1)) :=
    (hdc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hs,hx⟩)).integrableOn_compact isCompact_Icc
  obtain ⟨hdivi,hdivzero⟩ := periodic_C1_divergence_integrable_zero
    (fun x i => V s x i*A s x) (hflux s hs) (hperiod s hs)
  have he : (∫ x in angleBox (n+1), lieStep V A s x)=
      ∫ x in angleBox (n+1), deriv (fun t => A t x) s := by
    simp only [IsingBulk.Lie.lieStep]
    rw [integral_sub hdi hdivi,hdivzero,sub_zero]
  refine ⟨hdi.sub hdivi,?_⟩
  rw [he]
  exact hder

 theorem periodic_sector_iterate_lieStep_integral_on {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ) (j : ℕ)
    (hc : ∀ k < j, ContinuousOn
      (fun p : ℂ × AngularSpace n => ((lieStep V)^[k] A) p.1 p.2) (U ×ˢ angleBox (n+1)))
    (hdc : ∀ k < j, ContinuousOn (fun p : ℂ × AngularSpace n =>
      deriv (fun t => ((lieStep V)^[k] A) t p.2) p.1) (U ×ˢ angleBox (n+1)))
    (hd : ∀ k < j, ∀ s ∈ U, ∀ x ∈ angleBox (n+1),
      DifferentiableAt ℂ (fun t => ((lieStep V)^[k] A) t x) s)
    (hflux : ∀ k < j, ∀ s ∈ U, ∀ i,
      ContDiff ℝ 1 (fun x => V s x i*((lieStep V)^[k] A) s x))
    (hperiod : ∀ k < j, ∀ s ∈ U, ∀ i,
      CoordinatePeriodic (n+1) (fun x => V s x i*((lieStep V)^[k] A) s x)) :
    EqOn (fun s => ∫ x in angleBox (n+1), ((lieStep V)^[j] A) s x)
      (deriv^[j] (fun s => ∫ x in angleBox (n+1), A s x)) U := by
  induction j with
  | zero => intro s hs; rfl
  | succ j ih =>
    have hprev := ih (fun k hk => hc k (by omega)) (fun k hk => hdc k (by omega))
      (fun k hk => hd k (by omega)) (fun k hk => hflux k (by omega))
      (fun k hk => hperiod k (by omega))
    intro s hs
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    calc
      _ = deriv (fun t => ∫ x in angleBox (n+1), ((lieStep V)^[j] A) t x) s :=
        (periodic_sector_lie_step hU V _ (hc j (by omega)) (hdc j (by omega))
          (hd j (by omega)) (hflux j (by omega)) (hperiod j (by omega)) hs).2.deriv.symm
      _ = _ := (hprev.eventuallyEq_of_mem (hU.mem_nhds hs)).deriv_eq

end
end IsingBulk.Tail

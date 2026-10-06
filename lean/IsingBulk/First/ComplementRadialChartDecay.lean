import IsingBulk.First.ComplementRadialCompact

/-! Source-instantiated local complement decay on the actual compact radial
family. No compact-family regularity or transpose estimate remains as an input. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem selected_radial_chart_decay {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b : ℝ) : ℂ))
    (u₀ : DoubleAngularVector (2*p))
    (hgood : ¬ selectedBadConfiguration a b (angleTuple 1 u₀.1) (angleTuple 1 u₀.2))
    (J : Finset (SingularFactorIndex (2*p)))
    (hJ : ∀ f, f ∈ J ↔ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)
      (2*PrimeFamily.cosineAverage p a b) f) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ w : DoubleAngularVector (2*p) → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc 0 ε₀, ∀ η ∈ auxiliarySimplex J, ∀ t ∈ Icc (0:ℝ) 1,
      ∀ R : ℝ, 0 < R →
        ‖∫ u, sourceIBPAmplitude w J j (sourceRadialIBPParameter J θ ε η t) u *
          Complex.exp ((R : ℂ) * sourceIBPPhase J (sourceRadialIBPParameter J θ ε η t) u)‖ ≤
          R⁻¹ ^ q * C := by
  obtain ⟨e,δ,ρ,hδ,hρ,hchart⟩ := selected_source_active_chart hp hp11 ha hb
    (Complex.exp ((θ : ℂ)*Complex.I)) (Complex.exp_ne_zero _) hS u₀ hgood J hJ
  obtain ⟨d₀,hd₀,hdamp⟩ := sourceRadialPair_closed_damping hθ
  have hn : ∀ᶠ ε : ℝ in 𝓝 0,
      dist (sourceRadialPair θ ε) (sourceRadialPair θ 0) < ρ/2 := by
    exact (sourceRadialPair_continuous θ).continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨d,hd,hclose⟩ := Metric.eventually_nhds_iff.mp hn
  let ε₀ := min d₀ (d/2)
  have he₀ : 0 < ε₀ := lt_min hd₀ (by positivity)
  have hsmall (ε : ℝ) (hε : ε ∈ Icc 0 ε₀) :
      dist (sourceRadialPair θ ε) (1,Complex.exp ((θ : ℂ)*Complex.I)) < ρ/2 := by
    rw [← sourceRadialPair_zero]
    apply hclose
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hε.1]
    exact hε.2.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hlocal (ε : ℝ) (hε : ε ∈ Icc 0 ε₀) (u : DoubleAngularVector (2*p))
      (hu : u ∈ Metric.closedBall u₀ (ρ/2)) :
      (sourceRadialPair θ ε,u) ∈ sourceInactiveDomain J ∧
      ∀ f ∈ J, δ ≤ angularDot e (dampedSingularVector (sourceRadialPair θ ε).1
        (torusShift (fun _ => 1) u.1) (torusShift (fun _ => 1) u.2) f) := by
    apply hchart
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(hsmall ε hε).trans (by linarith), (Metric.mem_closedBall.mp hu).trans_lt (by linarith)⟩
  let K : Set (SourceIBPParameter J) :=
    (fun z : ℝ × (J → ℝ) × ℝ => sourceRadialIBPParameter J θ z.1 z.2.1 z.2.2) ''
      (Icc 0 ε₀ ×ˢ (auxiliarySimplex J ×ˢ Icc 0 1))
  have hK : IsCompact K := sourceRadialIBPParameter_compact J θ ε₀
  refine ⟨ρ/2,ε₀,by positivity,he₀,?_⟩
  intro w hw hsupp j q
  have hpK (k : SourceIBPParameter J) (hk : k ∈ K) :
      0 < k.1.1 ∧ k.1.1 ≤ 1 ∧ k.1.2 ≠ 0 ∧
      k.1.1⁻¹-k.1.1 ≤ (sourceS k.1.2).im ∧ k.2.1 ∈ auxiliarySimplex J := by
    obtain ⟨⟨ε,η,t⟩,⟨hε,hη,ht⟩,rfl⟩ := hk
    obtain ⟨hr,hr1,hs,hm⟩ := hdamp ε ⟨hε.1,hε.2.trans (min_le_left _ _)⟩
    exact ⟨hr,hr1,hs,hm,hη⟩
  have hdK (k : SourceIBPParameter J) (hk : k ∈ K) (u : DoubleAngularVector (2*p))
      (hu : u ∈ Metric.closedBall u₀ (ρ/2)) :
      ∀ f ∈ Jᶜ, sourceFactorDenominator k.1.2 (angleTuple k.1.1 u.1) (angleTuple k.1.1 u.2) f ≠ 0 := by
    obtain ⟨⟨ε,η,t⟩,⟨hε,hη,ht⟩,rfl⟩ := hk
    exact (hlocal ε hε u hu).1.2.2
  have hsK (k : SourceIBPParameter J) (hk : k ∈ K) (u : DoubleAngularVector (2*p))
      (hu : u ∈ Metric.closedBall u₀ (ρ/2)) :
      ∀ f ∈ J, δ ≤ angularDot e (dampedSingularVector k.1.1
        (torusShift (fun _ => 1) u.1) (torusShift (fun _ => 1) u.2) f) := by
    obtain ⟨⟨ε,η,t⟩,⟨hε,hη,ht⟩,rfl⟩ := hk
    exact (hlocal ε hε u hu).2
  obtain ⟨C,hC,hbound⟩ := source_uniform_nonstationary_decay w hw J
    (fun f hf => active_source_factor_valid f ((hJ f).mp hf)) hK (isCompact_closedBall u₀ (ρ/2))
    hsupp e δ hδ hpK hdK hsK j q
  refine ⟨C,hC,?_⟩
  intro ε hε η hη t ht R hR
  exact hbound _ ⟨(ε,η,t),⟨hε,hη,ht⟩,rfl⟩ R hR

end
end IsingBulk.First

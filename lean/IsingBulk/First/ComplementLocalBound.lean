import IsingBulk.First.ComplementAuxiliaryTailBound
import IsingBulk.First.ComplementSmallAuxiliary
import IsingBulk.First.ComplementAuxiliaryMajorant
import IsingBulk.First.SourceAuxiliaryInterchange

/-! Actual local complement estimate: every fixed complex temperature
derivative of the literal lifted angular integral stays bounded on the radial
approach. All auxiliary convergence and derivative interchange are proved. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff

theorem selected_radial_local_integral_bound {p : ℕ} {a b : ℤ}
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
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ‖(deriv^[j] (fun s => ∫ u, localizedDoubleAngleDensity (sourceRadialPair θ ε).1 s w u))
          (sourceRadialPair θ ε).2‖ ≤ C := by
  obtain ⟨γ₁,e₁,hγ₁,he₁,htail⟩ := selected_radial_chart_auxiliary_tail hp hp11 ha hb θ hθ hS u₀ hgood J hJ
  obtain ⟨γ₀,e₀,hγ₀,he₀,hsmall⟩ := source_radial_small_auxiliary_bound θ
    (2*PrimeFamily.cosineAverage p a b) hθ hS u₀ J hJ
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  let γ := min γ₀ γ₁
  let ε₀ := min e₀ (min e₁ (d/2))
  have hγ : 0 < γ := lt_min hγ₀ hγ₁
  have he : 0 < ε₀ := lt_min he₀ (lt_min he₁ (by positivity))
  refine ⟨γ,ε₀,hγ,he,?_⟩
  intro w hw hsupp j
  have hs₀ : tsupport w ⊆ Metric.closedBall u₀ γ₀ := hsupp.trans
    (Metric.closedBall_subset_closedBall (min_le_left _ _))
  have hs₁ : tsupport w ⊆ Metric.closedBall u₀ γ₁ := hsupp.trans
    (Metric.closedBall_subset_closedBall (min_le_right _ _))
  have hc : HasCompactSupport w := (isCompact_closedBall u₀ γ).of_isClosed_subset (isClosed_tsupport _) hsupp
  obtain ⟨C₀,hC₀,hbound₀⟩ := hsmall w hw hs₀ j
  obtain ⟨C₁,hC₁,hbound₁⟩ := htail w hw hs₁ j
  let G : (J → ℝ) → ℝ := fun ξ => ((2 : ℝ)^(Fintype.card J+1)*max C₀ C₁) *
    (1+‖ξ‖)^(-((Fintype.card J : ℝ)+1))
  have hG : Integrable G := auxiliary_small_large_majorant_integrable J C₀ C₁
  have hGpos (ξ) : 0 ≤ G ξ := by dsimp [G]; positivity
  refine ⟨∫ ξ in positiveAuxiliaryOrthant J, G ξ, integral_nonneg hGpos,?_⟩
  intro ε hε hεmax
  have hε₀ : ε ∈ Icc 0 e₀ := ⟨hε.le,hεmax.trans (min_le_left _ _)⟩
  have hε₁ : ε ≤ e₁ := hεmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd : ε < d := hεmax.trans_lt
    (((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith))
  have hmargin := (hm ε hε hεd (IsingBulk.Branch.radialParameter θ ε)
    (by simpa using mul_pos (show 0 < Real.sin θ/16 by positivity) hε)).2
  have hr : 0 < (sourceRadialPair θ ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair θ ε).1 < 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) hε
  have hEq := (sourceAuxiliaryDensity_integrated_jets (2*p) (Nat.mul_pos (by omega) hp.pos)
    hr hr1 w hw hc J (fun f hf => active_source_factor_valid f ((hJ f).mp hf))
    volume le_rfl (dampingDomain_of_margin hr hr1 hmargin) j).2
  rw [← iteratedDeriv_eq_iterate]
  change ‖iteratedDeriv j (fun s => ∫ u : DoubleAngularVector (2*p),
    localizedDoubleAngleDensity (sourceRadialPair θ ε).1 s w u)
      (IsingBulk.Branch.radialParameter θ ε)‖ ≤ _
  rw [hEq]
  simp only [iteratedDeriv_eq_iterate]
  change ‖∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
    ∫ u, sourceAuxiliaryJet (sourceRadialPair θ ε).1 (sourceRadialPair θ ε).2 w J j ξ u‖ ≤ _
  apply norm_integral_le_of_norm_le hG.integrableOn
  have horth : MeasurableSet (positiveAuxiliaryOrthant J) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi)
  filter_upwards [ae_restrict_mem horth] with ξ hξ
  exact auxiliary_small_large_majorant _ C₀ C₁ hC₀ hC₁ (hbound₀ ε hε₀)
    (hbound₁ ε hε hε₁) ξ (fun f => le_of_lt (hξ f (Set.mem_univ f)))

/-- The normalized local form-factor integral keeps the original N! outside. -/
def liftedLocalizedDoubleFormFactor (N : ℕ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * ∫ u, localizedDoubleAngleDensity r s w u

end
end IsingBulk.First

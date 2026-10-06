import IsingBulk.Tail.SelectorHypotheses
import IsingBulk.Tail.SelectorWeights

/-! Closed supports of the actual named Stokes multiplier for the same
constructed selector used by selected F. No all-branch current sector occurs. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff

theorem periodicUpperA_deriv_zero_above {α θ : ℝ} (hα : 0 < α)
    (hθ : 3*α/2 < Real.sin θ) : deriv (periodicUpperA α) θ=0 := by
  have he : periodicUpperA α =ᶠ[𝓝 θ] (fun _ => 1) := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds hθ)] with t ht
    exact thresholdStep_one (by linarith) ht.le
  simpa using he.deriv_eq

theorem current_named_plateau_tsupport {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (q : Fin N) {θ : Fin N → ℝ} (hθ : θ ∈ tsupport (namedSelectorDerivative f q)) :
    f.p (θ q)=1 ∧ deriv f.p (θ q)=0 ∧ f.m (θ q)=0 ∧ deriv f.m (θ q)=0 := by
  have hp := hf.p_smooth.continuous
  have hm := hf.m_smooth.continuous
  have hpd : ContDiff ℝ ∞ (deriv f.p) := by apply ContDiff.deriv'; simpa using hf.p_smooth
  have hmd : ContDiff ℝ ∞ (deriv f.m) := by apply ContDiff.deriv'; simpa using hf.m_smooth
  have hp' := hpd.continuous
  have hm' := hmd.continuous
  have hc : IsClosed {θ : Fin N → ℝ | f.p (θ q)=1 ∧ deriv f.p (θ q)=0 ∧
      f.m (θ q)=0 ∧ deriv f.m (θ q)=0} := by
    simp only [ofPred_and]
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        ((isClosed_eq (by fun_prop) continuous_const).inter
          (isClosed_eq (by fun_prop) continuous_const)))
  have hsub : tsupport (namedSelectorDerivative f q) ⊆
      {θ : Fin N → ℝ | f.p (θ q)=1 ∧ deriv f.p (θ q)=0 ∧
        f.m (θ q)=0 ∧ deriv f.m (θ q)=0} := by
    apply closure_minimal _ hc
    intro θ hn
    exact hf.named (θ q) (namedSelectorDerivative_support f θ q hn).1
  exact hsub hθ

theorem constructed_current_support_sine_upper {N : ℕ} (b η α : ℝ) (hα : 0 < α)
    (q i : Fin N) :
    tsupport (namedSelectorDerivative (constructedSelector b η α) q) ⊆
      {θ : Fin N → ℝ | Real.sin (θ i) ≤ 3*α/2} := by
  apply closure_minimal
  · intro θ hθ
    obtain ⟨hnq,hni⟩ := namedSelectorDerivative_support (constructedSelector b η α) θ q hθ
    by_contra hn
    have hs : 3*α/2 < Real.sin (θ i) := lt_of_not_ge hn
    by_cases hi : i=q
    · subst i
      exact hnq (periodicUpperA_deriv_zero_above hα hs)
    · exact hni i hi (thresholdStep_one (by linarith) hs.le)
  · exact isClosed_le (Real.continuous_sin.comp (continuous_apply i)) continuous_const

theorem constructed_current_support_sine_lower {N : ℕ} (b η α : ℝ) (hα : 0 < α)
    (q : Fin N) :
    tsupport (namedSelectorDerivative (constructedSelector b η α) q) ⊆
      {θ : Fin N → ℝ | α ≤ Real.sin (θ q)} := by
  apply closure_minimal
  · intro θ hθ
    have hn := (namedSelectorDerivative_support (constructedSelector b η α) θ q hθ).1
    exact upperA_support_sine α hα (support_deriv_subset hn)
  · exact isClosed_le continuous_const (Real.continuous_sin.comp (continuous_apply q))

/-- All support assertions are on the closed actual named-current support,
so zero values of a' at support boundary points cause no lost sector. -/
theorem constructed_current_support_geometry {N : ℕ} (b η α : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α)
    (q : Fin N) {θ : Fin N → ℝ}
    (hθ : θ ∈ tsupport (namedSelectorDerivative (constructedSelector b η α) q)) :
    (constructedSelector b η α).p (θ q)=1 ∧
      (constructedSelector b η α).m (θ q)=0 ∧ α ≤ Real.sin (θ q) ∧
      (∀ i, Real.sin (θ i) ≤ 3*α/2) ∧ η^2/2 ≤ lowerChord b (θ q) := by
  have hreg := constructedSelector_regular b η α hb hη hηsmall hα
  have hplateau := current_named_plateau_tsupport _ hreg q hθ
  have hlo := constructed_current_support_sine_lower b η α hα q hθ
  have hhi (i : Fin N) := constructed_current_support_sine_upper b η α hα q i hθ
  refine ⟨hplateau.1,hplateau.2.2.1,hlo,hhi,?_⟩
  have hs : 0 ≤ Real.sin (θ q) := hα.le.trans hlo
  have hsq : (Real.sin b)^2 ≤ lowerChord b (θ q) := by
    unfold lowerChord
    nlinarith [sq_nonneg (Real.cos (θ q)-Real.cos b),sq_nonneg (Real.sin (θ q)),
      mul_nonneg hs hb.le]
  have hsmall : η^2/2 ≤ (Real.sin b)^2 := by nlinarith
  exact hsmall.trans hsq

/-- Every finite angular jet retains the named plateaus; the named upper
index cannot turn into a true branch index under differentiation. -/
theorem current_named_jet_plateau {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (q : Fin N) (j : ℕ) {θ : Fin N → ℝ}
    (hθ : θ ∈ tsupport (iteratedFDeriv ℝ j (namedSelectorDerivative f q))) :
    f.p (θ q)=1 ∧ deriv f.p (θ q)=0 ∧ f.m (θ q)=0 ∧ deriv f.m (θ q)=0 :=
  current_named_plateau_tsupport f hf q (tsupport_iteratedFDeriv_subset j hθ)

theorem constructed_current_not_all_branch {N : ℕ} (b η α : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α)
    (q : Fin N) {θ : Fin N → ℝ}
    (hθ : θ ∈ tsupport (namedSelectorDerivative (constructedSelector b η α) q)) :
    ¬ (∀ i, (constructedSelector b η α).m (θ i)=1) := by
  have hm := (constructed_current_support_geometry b η α hb hη hηsmall hα q hθ).2.1
  intro hall
  have h := hall q
  rw [hm] at h
  norm_num at h

end
end IsingBulk.Tail

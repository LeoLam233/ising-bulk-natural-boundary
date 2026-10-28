import IsingBulk.HT22.Far.UnscaledShell
import IsingBulk.HT22.Far.AggregateBudget

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The actual unscaled physical measure on one labeled signed shell. -/
def physicalShellMass {n : ℕ} (a η : ℝ) (b : PreferredBranchData) (B : PreferredCoareaBump b)
    (δ τ ε r : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (l : ℤ) (i k : Fin (n+1)) : ℝ≥0∞ :=
  ∫⁻ x in signedRightShell a b B δ r l i k,
    ENNReal.ofReal ‖transportedDensity (Complex.exp (-Complex.I*(η:ℂ))) τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAtTotal a x))‖

/-- Full far dyadic/mean/extrema sum. No scale cap or source estimate is a
premise; the infinite shell sum is reduced to a uniformly finite prefix. -/
theorem actual_far_shell_sum (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ δ₀ : ℝ, 0<δ₀ → ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
    ∀ a η : ℝ, ∀ m : ℕ, ∀ ε τ : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → ∀ δ : ℝ, δ≤δB →
    (∑' q : ℕ, ∑ l : {l : ℤ // l∈preferredMeanIndices (m+3)},
      ∑ i : Fin (m+3), ∑ k : Fin (m+3),
      if δ₀≤shellCoordinateScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((m+3:ℕ):ℝ))
          (preferredDyadicRadius q) ε then
        physicalShellMass a η b B δ τ ε (preferredDyadicRadius q) rcut j l.1 i k else 0) ≤
      ENNReal.ofReal (farOrderEnvelope A L (m+3)*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_far_unscaled_dyadic_shell b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro δ₀ hδ₀ rcut hrcut hrper j
  obtain ⟨A,L,hA,hsource⟩ := hsource δ₀ hδ₀ rcut hrcut hrper j
  obtain ⟨K,hK⟩ := far_dyadic_prefix hδ₀
  refine ⟨max 1 (3*(K:ℝ))*A,L+3,by positivity,?_⟩
  intro a η m ε τ hε hεr hτ hτr δ hδ
  let f : ℕ → {l : ℤ // l∈preferredMeanIndices (m+3)} → Fin (m+3) → Fin (m+3) → ℝ≥0∞ :=
    fun q l i k => if δ₀≤shellCoordinateScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((m+3:ℕ):ℝ))
      (preferredDyadicRadius q) ε then
      physicalShellMass a η b B δ τ ε (preferredDyadicRadius q) rcut j l.1 i k else 0
  let E := farOrderEnvelope A L (m+3)*(1+|Real.log ε|)
  have hE : 0≤E := mul_nonneg (farOrderEnvelope_nonneg hA.le _ _) (by positivity)
  have hf : ∀ q l i k,f q l i k≤ENNReal.ofReal E := by
    intro q l i k
    dsimp only [f]
    split_ifs with hfar
    · exact hsource a η m ε τ hε hεr hτ hτr q l.1 hfar δ hδ i k
    · exact bot_le
  have hz : ∀ q,K≤q → ∀ l i k,f q l i k=0 := by
    intro q hq l i k
    have hn : ¬δ₀≤shellCoordinateScale (b.b+(a+2*Real.pi*(l.1:ℝ))/((m+3:ℕ):ℝ))
        (preferredDyadicRadius q) ε := by
      intro hfar
      exact (not_lt_of_ge hq) (hK _ ε hε.le q hfar)
    dsimp only [f]
    simp only [ite_eq_right_iff]
    intro h
    exact (hn h).elim
  have hh := finite_shell_label_sum_bound (show 0<m+3 by omega) f (ENNReal.ofReal E) hf hz
  change (∑' q,∑ l,∑ i,∑ k,f q l i k)≤_
  apply hh.trans
  rw [←ENNReal.ofReal_natCast (3*K*(m+3)^3),←ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [E]
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (far_label_envelope_absorb hA.le K L (m+3) (by omega)) (by positivity)

end
end IsingBulk.HT22.Far

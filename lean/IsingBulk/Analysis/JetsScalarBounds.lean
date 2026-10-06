import IsingBulk.Analysis.JetsBoundCalculus
import IsingBulk.Analysis.JetsLocalChart

/-! All scalar neighborhoods and constants here are chosen before the number
of angular variables. In particular these neighborhoods contain the diagonal. -/
namespace IsingBulk.Jets
noncomputable section
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def pairFactor (a : Fin 4) (z : ℂ × ℂ × ℂ) : ℂ :=
  ![selectedRegularFactor z.1 z.2.1 z.2.2,
    regularG z.1 z.2.2*Complex.sin z.2.1/selectedDenominator z.1 z.2.1 z.2.2,
    regularG z.1 z.2.1*Complex.sin z.2.2/selectedDenominator z.1 z.2.1 z.2.2,
    z.2.2-z.2.1] a

@[simp]
theorem pairFactor_one (z : ℂ × ℂ × ℂ) : pairFactor 1 z =
    regularG z.1 z.2.2*Complex.sin z.2.1/selectedDenominator z.1 z.2.1 z.2.2 := rfl

@[simp]
theorem pairFactor_two (z : ℂ × ℂ × ℂ) : pairFactor 2 z =
    regularG z.1 z.2.1*Complex.sin z.2.2/selectedDenominator z.1 z.2.1 z.2.2 := rfl

theorem pairFactor_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (a : Fin 4) :
    AnalyticAt ℂ (pairFactor a) (s,0,0) := by
  have hg := regularG_analytic_base s c hs hS hc
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.1) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2)
      (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) hg (by fun_prop)
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.2) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2)
      (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) hg (by fun_prop)
  have hd := selectedDenominator_analytic_base s c hs hS hc
  have hn : selectedDenominator s 0 0 ≠ 0 := by
    rw [selectedDenominator_base]
    exact regularG_base_ne_zero s c hS hc
  fin_cases a
  · exact selectedRegularFactor_analytic_base s c hs hS hc
  · exact (hq.mul (by fun_prop)).div hd hn
  · exact (hp.mul (by fun_prop)).div hd hn
  · change AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.2-z.2.1) (s,0,0)
    fun_prop

theorem finite_family_jet_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : ℕ} (f : Fin M → E → ℂ) (z : E) (h : ∀ a, AnalyticAt ℂ (f a) z) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ y in 𝓝 z, ∀ a, JetBound (f a) y J C := by
  have hb := fun a => finite_analytic_jets_bounded (f a) z (h a) J
  choose C hC hb using hb
  let D : ℝ := 1+∑ a, C a
  have hDC : ∀ a, C a ≤ D := by
    intro a
    have hh := Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => (hC b).le)
      (Finset.mem_univ a)
    dsimp [D]
    linarith
  refine ⟨D,by
    have hh : 0 ≤ ∑ a, C a := Finset.sum_nonneg (fun a _ => (hC a).le)
    dsimp [D]; linarith,?_⟩
  have he : ∀ᶠ y in 𝓝 z, ∀ a, AnalyticAt ℂ (f a) y ∧ ∀ k ≤ J,
      ‖iteratedFDeriv ℂ k (f a) y‖ ≤ C a :=
    Filter.eventually_all.mpr (fun a => (h a).eventually_analyticAt.and (hb a))
  filter_upwards [he] with y hy
  exact fun a => ⟨(hy a).1,(hC a).le.trans (hDC a),
    fun k hk => ((hy a).2 k hk).trans (hDC a)⟩

def pairCoordinate {N : ℕ} (p q : Fin N) :
    (ℂ × (Fin N → ℂ)) →L[ℂ] (ℂ × ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
    (((ContinuousLinearMap.proj (R := ℂ) p).prod (ContinuousLinearMap.proj (R := ℂ) q)).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)))

theorem pairCoordinate_norm {N : ℕ} (p q : Fin N) : ‖pairCoordinate p q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖(z.1,z.2 p,z.2 q)‖ ≤ 1*‖z‖
  simp only [one_mul,Prod.norm_def]
  exact max_le (le_max_left _ _) (max_le
    ((norm_le_pi_norm z.2 p).trans (le_max_right _ _))
    ((norm_le_pi_norm z.2 q).trans (le_max_right _ _)))

structure ScalarBounds {N : ℕ} (p q : Fin N) (z : ℂ × (Fin N → ℂ))
    (J : ℕ) (C : ℝ) : Prop where
  one_le : 1 ≤ C
  coefficient : CoefficientPoint p q z
  a : ∀ i, JetBound (fun t : ℂ × ℂ => regularA t.1 t.2) (z.1,z.2 i) J C
  pair : ∀ a, JetBound (pairFactor a) (z.1,z.2 p,z.2 q) J C

theorem scalar_bounds_uniform (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ U : Set (ℂ × ℂ), ∃ P : Set (ℂ × ℂ × ℂ),
      IsOpen U ∧ (s,0) ∈ U ∧ IsOpen P ∧ (s,0,0) ∈ P ∧
      ∀ N : ℕ, ∀ p q : Fin N, ∀ z : ℂ × (Fin N → ℂ),
        (∀ i, (z.1,z.2 i) ∈ U) → (z.1,z.2 p,z.2 q) ∈ P → ScalarBounds p q z J C := by
  obtain ⟨U₀,P₀,hU₀,hsU₀,hP₀,hsP₀,hpoint⟩ := coefficient_neighborhoods s c hs hS hc
  obtain ⟨C,hC,hb⟩ := finite_family_jet_bounds
    (fun _ : Fin 1 => fun t : ℂ × ℂ => regularA t.1 t.2) (s,0)
    (fun _ => regularA_analytic_base s c hs hS hc) J
  obtain ⟨D,hD,hd⟩ := finite_family_jet_bounds pairFactor (s,0,0)
    (pairFactor_analytic_base s c hs hS hc) J
  obtain ⟨U₁,hU₁,ho₁,hx₁⟩ := eventually_nhds_iff.mp hb
  obtain ⟨P₁,hP₁,ho₂,hx₂⟩ := eventually_nhds_iff.mp hd
  refine ⟨C+D,by linarith,U₀∩U₁,P₀∩P₁,hU₀.inter ho₁,⟨hsU₀,hx₁⟩,
    hP₀.inter ho₂,⟨hsP₀,hx₂⟩,?_⟩
  intro N p q z hz hp
  refine ⟨by linarith,hpoint N p q z (fun i => (hz i).1) hp.1,?_,?_⟩
  · intro i
    exact (hU₁ _ (hz i).2 0).mono le_rfl (by linarith)
  · intro a
    exact (hP₁ _ hp.2 a).mono le_rfl (by linarith)

end
end IsingBulk.Jets

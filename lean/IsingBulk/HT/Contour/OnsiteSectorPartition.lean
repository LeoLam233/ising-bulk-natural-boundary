import IsingBulk.HT.Contour.OnsiteLieIntegration
import IsingBulk.HT.Contour.OnsiteWeightedAngularJets
import IsingBulk.HT.Contour.OnsiteRetraction
import IsingBulk.Tail.SectorIntegralDecomposition

/-! Exact finite assignment reconstruction of the actual onsite K and every
named current, including all derivatives with the radius fixed. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

def onsiteOriginalSectorIntegral (N : ℕ) (f : SelectorFunctions) (r τ b inner : ℝ)
    (hi : 0< inner) (sigma : Fin N → Fin 3) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N,onsiteOriginalSectorWeight f b inner hi sigma θ*onsitePulledDensity f r τ 0 s θ

def onsiteNamedSectorIntegral (N : ℕ) (f : SelectorFunctions) (r τ lam b inner : ℝ)
    (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N,onsiteNamedSectorWeight f b inner hi q sigma τ θ*onsitePulledDensity f r τ lam s θ

theorem onsiteOriginalSectorWeight_sum (N : ℕ) (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (θ : Fin N → ℝ) :
    (∑ sigma,onsiteOriginalSectorWeight f b inner hi sigma θ)=(angularSelector f θ:ℂ) := by
  unfold onsiteOriginalSectorWeight
  rw [← Complex.ofReal_sum,← Finset.mul_sum,sector_assignment_partition,mul_one]

theorem onsiteNamedSectorWeight_sum (N : ℕ) (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) (τ : ℝ) (θ : Fin N → ℝ) :
    (∑ sigma,onsiteNamedSectorWeight f b inner hi q sigma τ θ)=namedCurrentMultiplier f τ q θ := by
  unfold onsiteNamedSectorWeight namedCurrentMultiplier
  rw [← Finset.mul_sum,← Complex.ofReal_sum,← Finset.mul_sum,sector_assignment_partition,mul_one]

/-- A finite family of fixed real-chart weights commutes with every
parameter derivative, by actual source holomorphy. -/
theorem onsite_weight_family_iteratedDeriv {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0<N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ lam : ℝ} (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    (w : (Fin N → ℝ) → ℂ) (weights : ι → (Fin N → ℝ) → ℂ)
    (hweights : ∀ i,Continuous (weights i)) (hsum : ∀ θ,∑ i,weights i θ=w θ)
    {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (fun z => ∫ θ in angleBox N,w θ*onsitePulledDensity f r τ lam z θ) s=
      ∑ i,iteratedDeriv j (fun z => ∫ θ in angleBox N,weights i θ*onsitePulledDensity f r τ lam z θ) s := by
  classical
  have he : (fun z => ∫ θ in angleBox N,w θ*onsitePulledDensity f r τ lam z θ) =ᶠ[𝓝 s]
      (fun z => ∑ i,∫ θ in angleBox N,weights i θ*onsitePulledDensity f r τ lam z θ) := by
    filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
    have hD := (onsite_fixedDensity_contDiff hN f hf hr hr1 hτ hlam z hz.2).continuous
    have hint (i : ι) : IntegrableOn
        (fun θ => weights i θ*onsitePulledDensity f r τ lam z θ) (angleBox N) :=
      ((hweights i).mul hD).continuousOn.integrableOn_compact isCompact_Icc
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    dsimp only
    rw [← Finset.sum_mul,hsum]
  rw [he.iteratedDeriv_eq j]
  apply iteratedDeriv_fun_sum
  intro i _
  exact (onsite_weighted_homotopy_slice_analytic N hN f hf hr hr1 hτ hlam
    (weights i) (hweights i) s hs).contDiffAt

theorem onsite_originalLower_sector_derivative (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (b inner : ℝ) (hi : 0< inner)
    {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (onsiteOriginalLowerIntegral N f r τ) s=
      ∑ sigma,iteratedDeriv j (onsiteOriginalSectorIntegral N f r τ b inner hi sigma) s :=
  onsite_weight_family_iteratedDeriv N hN f hf hr hr1 hτ le_rfl _
    (onsiteOriginalSectorWeight f b inner hi)
    (fun sigma => (onsiteOriginalSectorWeight_smooth f hf b inner hi sigma).continuous)
    (onsiteOriginalSectorWeight_sum N f b inner hi) hs j

theorem onsite_namedCurrent_sector_derivative (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (onsiteActualNamedCurrentIntegral N f r τ lam q) s=
      ∑ sigma,iteratedDeriv j (onsiteNamedSectorIntegral N f r τ lam b inner hi q sigma) s :=
  onsite_weight_family_iteratedDeriv N hN f hf hr hr1 hτ hlam _
    (fun sigma => onsiteNamedSectorWeight f b inner hi q sigma τ)
    (fun sigma => (onsiteNamedSectorWeight_smooth f hf b inner hi q sigma τ).continuous)
    (onsiteNamedSectorWeight_sum N f b inner hi q τ) hs j

/-- The complete differentiated slice equals the finite sum of actual
sector derivatives. All named indices and every assignment remain present. -/
theorem onsite_differentiatedCurrentSlice_sector_derivative (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hlam : 0≤lam)
    (b inner : ℝ) (hi : 0< inner) {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) :
    onsiteDifferentiatedCurrentSlice N f r τ lam j s=
      ∑ q : Fin N,∑ sigma,
        iteratedDeriv j (onsiteNamedSectorIntegral N f r τ lam b inner hi q sigma) s := by
  rw [onsiteDifferentiatedCurrentSlice_source_formula]
  apply Finset.sum_congr rfl
  intro q _
  have he := (onsite_weightedAngularIntegral_jets N hN f hf hr hr1 hτ hlam
    (namedCurrentMultiplier f τ q) (namedCurrentMultiplier_continuous f hf τ q) s hs j).1
  calc
    _ = iteratedDeriv j (onsiteActualNamedCurrentIntegral N f r τ lam q) s := he.symm
    _ = _ := onsite_namedCurrent_sector_derivative N hN f hf hr hr1 hτ hlam b inner hi q hs j

end
end IsingBulk.HT.Contour

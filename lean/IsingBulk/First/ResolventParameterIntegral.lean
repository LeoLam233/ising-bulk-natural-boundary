import IsingBulk.First.CompactParameterIntegral
import IsingBulk.First.ContourDefinitions

/-! Analytic parameter dependence of finite products of the actual source
resolvents, integrated over a compact measured domain. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def sourceResolventProduct {A : Type*} {N : ℕ} (B : Fin N → A → ℂ) (s : ℂ) (a : A) : ℂ :=
  ∏ i, (sourceS s-B i a)⁻¹

def sourceResolventDerivative {A : Type*} {N : ℕ} (B : Fin N → A → ℂ) (s : ℂ) (a : A) : ℂ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, (sourceS s-B j a)⁻¹) *
    (-(1-s⁻¹^2)/(sourceS s-B i a)^2)

theorem sourceResolventProduct_hasDerivAt {A : Type*} {N : ℕ} (B : Fin N → A → ℂ)
    (s : ℂ) (a : A) (hs : s ≠ 0) (hB : ∀ i, sourceS s-B i a ≠ 0) :
    HasDerivAt (fun t => sourceResolventProduct B t a) (sourceResolventDerivative B s a) s := by
  have hS : HasDerivAt sourceS (1-s⁻¹^2) s := by
    convert! (hasDerivAt_id s).add ((hasDerivAt_id s).inv hs) using 1;
      simp [div_eq_mul_inv, inv_pow, sub_eq_add_neg]
  have hd (i : Fin N) : HasDerivAt (fun t => (sourceS t-B i a)⁻¹)
      (-(1-s⁻¹^2)/(sourceS s-B i a)^2) s := by
    exact (hS.sub_const (B i a)).inv (hB i)
  simpa only [sourceResolventProduct, sourceResolventDerivative, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i)

theorem sourceResolvents_continuousOn {A : Type*} [TopologicalSpace A] {N : ℕ}
    (B : Fin N → A → ℂ) (hB : ∀ i, Continuous (B i)) {U : Set ℂ}
    (hU : ∀ s ∈ U, s ≠ 0) (hD : ∀ s ∈ U, ∀ a, ∀ i, sourceS s-B i a ≠ 0) :
    ContinuousOn (fun p : ℂ × A => sourceResolventProduct B p.1 p.2) (U ×ˢ univ) ∧
    ContinuousOn (fun p : ℂ × A => sourceResolventDerivative B p.1 p.2) (U ×ˢ univ) := by
  have hsinv : ContinuousOn (fun p : ℂ × A => p.1⁻¹) (U ×ˢ univ) :=
    continuous_fst.continuousOn.inv₀ (fun p hp => hU p.1 hp.1)
  have hS : ContinuousOn (fun p : ℂ × A => sourceS p.1) (U ×ˢ univ) :=
    continuous_fst.continuousOn.add hsinv
  have hd (i : Fin N) : ContinuousOn (fun p : ℂ × A => sourceS p.1-B i p.2) (U ×ˢ univ) :=
    hS.sub ((hB i).comp continuous_snd).continuousOn
  have hi (i : Fin N) : ContinuousOn (fun p : ℂ × A => (sourceS p.1-B i p.2)⁻¹) (U ×ˢ univ) :=
    (hd i).inv₀ (fun p hp => hD p.1 hp.1 p.2 i)
  constructor
  · exact continuousOn_finsetProd Finset.univ (fun i _ => hi i)
  · apply continuousOn_finsetSum Finset.univ
    intro i _
    apply (continuousOn_finsetProd (Finset.univ.erase i) (fun j _ => hi j)).mul
    exact ((continuousOn_const.sub (hsinv.pow 2)).neg).div ((hd i).pow 2)
      (fun p hp => pow_ne_zero 2 (hD p.1 hp.1 p.2 i))

/-- No regularity of an integral is assumed: compact domination is constructed
from the actual rational derivative and its joint continuity. -/
theorem resolventIntegral_differentiableAt {A : Type*} [TopologicalSpace A] [T2Space A]
    [MeasurableSpace A] [OpensMeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasureOnCompacts μ] {K : Set A} (hK : IsCompact K) {N : ℕ}
    (B : Fin N → A → ℂ) (hB : ∀ i, Continuous (B i)) (w : A → ℂ) (hw : Continuous w)
    {U : Set ℂ} {s : ℂ} (hsU : U ∈ 𝓝 s) (hU : ∀ t ∈ U, t ≠ 0)
    (hD : ∀ t ∈ U, ∀ a, ∀ i, sourceS t-B i a ≠ 0) :
    DifferentiableAt ℂ (fun t => ∫ a in K, w a*sourceResolventProduct B t a ∂μ) s := by
  obtain ⟨hP,hG⟩ := sourceResolvents_continuousOn B hB hU hD
  have hw' : ContinuousOn (fun p : ℂ × A => w p.2) (U ×ˢ K) :=
    (hw.comp continuous_snd).continuousOn
  apply (hasDerivAt_compact_integral hK hsU
    (fun t a => w a*sourceResolventProduct B t a)
    (fun t a => w a*sourceResolventDerivative B t a)
    (hw'.mul (hP.mono (prod_mono Subset.rfl (subset_univ K))))
    (hw'.mul (hG.mono (prod_mono Subset.rfl (subset_univ K)))) ?_).differentiableAt
  intro t ht a _ha
  exact (sourceResolventProduct_hasDerivAt B t a (hU t ht) (hD t ht a)).const_mul (w a)

end
end IsingBulk.First

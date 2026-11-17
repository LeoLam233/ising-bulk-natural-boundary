import IsingBulk.AnisoF002.C03.IsotropicNonbranchLocalRoot
import IsingBulk.AnisoF002.C03.IsotropicPhysicalParameter
import IsingBulk.AnisoF002.C03.IsotropicJointPhysicalAnalytic

/-!
# Actual joint analytic density near a nonresonant total coincidence

The continued expression keeps every physical pair and one-body factor,
the complete signed product kernel and the original normalization. Its
upper-side identity with the original density is proved, so this is a
local continuation of that density, not a substitute coefficient.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicRootPhysicalDensity {N : ℕ} (R : ℂ → ℂ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ)) : ℂ :=
  isotropicParticleNormalization N *
    ((1 + σ * ∏ i, R (isotropicDispersion (p.1, p.2 i))) /
      (1 - σ * ∏ i, R (isotropicDispersion (p.1, p.2 i)))) *
    (∏ i, 2 * R (isotropicDispersion (p.1, p.2 i)) /
      (1 - R (isotropicDispersion (p.1, p.2 i)) ^ 2)) *
    ∏ ij ∈ indexPairs N, canceledPair 1
      (R (isotropicDispersion (p.1, p.2 ij.1))) (R (isotropicDispersion (p.1, p.2 ij.2)))
      (Complex.exp (p.2 ij.1 * Complex.I)) (Complex.exp (p.2 ij.2 * Complex.I))

theorem isotropicRootPhysicalDensity_eq_actual {N : ℕ} (R : ℂ → ℂ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ))
    (hR : ∀ i, R (isotropicDispersion (p.1, p.2 i)) =
      upperEdgeRoot (isotropicDispersion (p.1, p.2 i))) :
    isotropicRootPhysicalDensity R σ p = isotropicBarePhysicalDensity p.1 σ p.2 := by
  unfold isotropicRootPhysicalDensity isotropicBarePhysicalDensity
  simp_rw [hR, ← isotropic_oneBody_eq_inverse_sinh]
  rfl

theorem isotropicNonresonantLocalDensity_analyticAt {N : ℕ} (S₀ μ : ℝ) (σ : ℂ)
    (hx : -1 < S₀ - Real.cos μ) (hx1 : S₀ - Real.cos μ ≠ 1)
    (hden : 1 - σ * upperBoundaryRoot (S₀ - Real.cos μ) ^ N ≠ 0) :
    AnalyticAt ℂ
      (isotropicRootPhysicalDensity (N := N) (isotropicNonbranchLocalRoot (S₀ - Real.cos μ)) σ)
      ((S₀ : ℂ), fun _ => (μ : ℂ)) := by
  let x := S₀ - Real.cos μ
  let p : ℂ × (Fin N → ℂ) := ((S₀ : ℂ), fun _ => (μ : ℂ))
  let R := isotropicNonbranchLocalRoot x
  have hw (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => q.2 i) p :=
    (show (Fin N → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i).analyticAt _ |>.comp analyticAt_snd
  have hd (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) =>
      isotropicDispersion (q.1, q.2 i)) p :=
    analyticAt_fst.sub (Complex.analyticAt_cos.comp (hw i))
  have hd0 (i : Fin N) : isotropicDispersion (p.1, p.2 i) = (x : ℂ) := by
    simp only [isotropicDispersion, p, x, ← Complex.ofReal_cos, Complex.ofReal_sub]
  have hr (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) =>
      R (isotropicDispersion (q.1, q.2 i))) p :=
    (isotropicNonbranchLocalRoot_analyticAt hx hx1).comp_of_eq (hd i) (hd0 i)
  have hr0 (i : Fin N) : R (isotropicDispersion (p.1, p.2 i)) = upperBoundaryRoot x := by
    rw [hd0]
    exact isotropicNonbranchLocalRoot_center hx hx1
  have hb0 (i : Fin N) : 1 - R (isotropicDispersion (p.1, p.2 i)) ^ 2 ≠ 0 := by
    rw [hr0]
    exact upperBoundaryRoot_oneBody_ne_zero hx hx1
  have hpair0 (i j : Fin N) : 1 - R (isotropicDispersion (p.1, p.2 i)) *
      R (isotropicDispersion (p.1, p.2 j)) ≠ 0 := by
    rw [hr0, ← pow_two]
    exact upperBoundaryRoot_oneBody_ne_zero hx hx1
  have hz (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) =>
      Complex.exp (q.2 i * Complex.I)) p := ((hw i).mul analyticAt_const).cexp'
  have hb (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) =>
      2 * R (isotropicDispersion (q.1, q.2 i)) /
        (1 - R (isotropicDispersion (q.1, q.2 i)) ^ 2)) p :=
    (analyticAt_const.mul (hr i)).div (analyticAt_const.sub ((hr i).pow 2)) (hb0 i)
  have hp (i j : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => canceledPair 1
      (R (isotropicDispersion (q.1, q.2 i))) (R (isotropicDispersion (q.1, q.2 j)))
      (Complex.exp (q.2 i * Complex.I)) (Complex.exp (q.2 j * Complex.I))) p := by
    unfold canceledPair
    apply (((analyticAt_const.mul (((hz i).sub (hz j)).pow 2)).mul (hr i)).mul (hr j)).div
      (((hz i).mul (hz j)).mul ((analyticAt_const.sub ((hr i).mul (hr j))).pow 2))
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
      (pow_ne_zero _ (hpair0 i j))
  have hprod : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) =>
      ∏ i, R (isotropicDispersion (q.1, q.2 i))) p :=
    Finset.univ.analyticAt_fun_prod fun i _ => hr i
  have hden0 : 1 - σ * ∏ i, R (isotropicDispersion (p.1, p.2 i)) ≠ 0 := by
    simpa only [hr0, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hden
  change AnalyticAt ℂ (isotropicRootPhysicalDensity R σ) p
  unfold isotropicRootPhysicalDensity
  exact ((analyticAt_const.mul
    ((analyticAt_const.add (analyticAt_const.mul hprod)).div
      (analyticAt_const.sub (analyticAt_const.mul hprod)) hden0)).mul
      (Finset.univ.analyticAt_fun_prod fun i _ => hb i)).mul
        ((indexPairs N).analyticAt_fun_prod fun ij _ => hp ij.1 ij.2)

theorem isotropicNonresonantLocalDensity_matches_upper {N : ℕ} (S₀ μ : ℝ) (σ : ℂ)
    (hx : -1 < S₀ - Real.cos μ) (hx1 : S₀ - Real.cos μ ≠ 1) :
    ∀ᶠ p : ℂ × (Fin N → ℂ) in 𝓝 ((S₀ : ℂ), fun _ => (μ : ℂ)),
      (∀ i, 0 < (isotropicDispersion (p.1, p.2 i)).im) →
      isotropicRootPhysicalDensity (isotropicNonbranchLocalRoot (S₀ - Real.cos μ)) σ p =
        isotropicBarePhysicalDensity p.1 σ p.2 := by
  have hall : ∀ᶠ p : ℂ × (Fin N → ℂ) in 𝓝 ((S₀ : ℂ), fun _ => (μ : ℂ)),
      ∀ i, 0 < (isotropicDispersion (p.1, p.2 i)).im →
        isotropicNonbranchLocalRoot (S₀ - Real.cos μ) (isotropicDispersion (p.1, p.2 i)) =
          upperEdgeRoot (isotropicDispersion (p.1, p.2 i)) := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun p : ℂ × (Fin N → ℂ) => isotropicDispersion (p.1, p.2 i)) := by
      unfold isotropicDispersion
      fun_prop
    have ht : Tendsto (fun p : ℂ × (Fin N → ℂ) => isotropicDispersion (p.1, p.2 i))
        (𝓝 ((S₀ : ℂ), fun _ => (μ : ℂ))) (𝓝 ((S₀ - Real.cos μ : ℝ) : ℂ)) := by
      simpa only [isotropicDispersion, ← Complex.ofReal_cos, Complex.ofReal_sub] using
        hc.continuousAt.tendsto (x := ((S₀ : ℂ), fun _ : Fin N => (μ : ℂ)))
    exact ht.eventually (isotropicNonbranchLocalRoot_matches_upper hx hx1)
  filter_upwards [hall] with p hp hupper
  exact isotropicRootPhysicalDensity_eq_actual _ σ p (fun i => hp i (hupper i))

end
end IsingBulk.AnisoF002.Isotropic

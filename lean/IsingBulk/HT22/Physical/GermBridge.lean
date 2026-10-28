import IsingBulk.HT22.Physical.ExteriorIdentity
import IsingBulk.HT.Final.PublishedPhysicalIdentification
import IsingBulk.HT.Final.RealGermUniqueness

/-!
# Identification of the analytic physical germ, including the removable origin

Finite-N exterior holomorphy and real-interval analytic uniqueness identify
the literal F001 coefficients with the established full-site coefficients.
Their full odd sums therefore agree on the exterior, not merely formally.
The limit at the removable interior origin is consequently proved to exist,
and both beta-free and beta-inclusive disk germs are identified unconditionally.
No old natural-boundary or completed boundary-tail endpoint is used.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.HT.Contour IsingBulk.HT.Final IsingBulk.Final Set Filter
open scoped Topology BigOperators

/-- Real odd-particle absolute convergence, proved from the previously verified
physical/angular-to-contour bridge and the interior right-chart majorant. This
is not the F001 boundary differentiated-tail theorem. -/
theorem oddSeries_real_norm_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℕ => ‖coefficient (2*n+1) (t:ℂ)‖) := by
  apply (physicalAngularOdd_norm_summable ht).congr
  intro n
  rw [coefficient_odd_eq_published n ht]

/-- Actual F001-to-existing-germ identity on the whole physical interval. -/
theorem puncturedInteriorBulk_real_eq_existing {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    puncturedInteriorBulk (x:ℂ) = interiorFullBulk (x:ℂ) :=
  (publishedBulk_eq_F001_real interiorFullBulk_publishedAngularRepresentation hx hx1).symm

/-- The already constructed disk germ is an analytic continuation of the exact
F001 angular real function; this is a witness, not an assumed continuation. -/
theorem existingBulk_is_analytic_F001_continuation :
    AnalyticOnNhd ℂ interiorFullBulk {s : ℂ | ‖s‖ < 1} ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      interiorFullBulk (x:ℂ) = puncturedInteriorBulk (x:ℂ)) := by
  exact ⟨interiorFullBulk_analyticOn,
    fun _ hx hx1 => (puncturedInteriorBulk_real_eq_existing hx hx1).symm⟩

/-- Any analytic continuation constructed from the literal F001 angular real
function must be this same HT germ, including at s=0. -/
theorem analytic_F001_continuation_eq_existing {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G {s : ℂ | ‖s‖ < 1})
    (hreal : ∀ x : ℝ, 0 < x → x < 1/16 →
      G (x:ℂ) = puncturedInteriorBulk (x:ℂ)) :
    EqOn G interiorFullBulk {s : ℂ | ‖s‖ < 1} := by
  apply analytic_unitDisk_eq_of_real_germ hG interiorFullBulk_analyticOn
  intro x hx hxsmall
  exact (hreal x hx hxsmall).trans
    (puncturedInteriorBulk_real_eq_existing hx (by linarith))

/-- Literal removable extension of the new angular sum. Existence of its limit
and its analyticity are theorems below, not encoded premises. -/
def interiorBulk : ℂ → ℂ :=
  Function.update puncturedInteriorBulk 0
    (limUnder (𝓝[≠] (0:ℂ)) puncturedInteriorBulk)

theorem interiorBulk_eq_punctured {s : ℂ} (hs : s ≠ 0) :
    interiorBulk s = puncturedInteriorBulk s :=
  Function.update_of_ne hs _ _

/-- Equality on an actual punctured neighborhood gives the complex limit at zero. -/
theorem puncturedInteriorBulk_tendsto_zero :
    Tendsto puncturedInteriorBulk (𝓝[≠] (0:ℂ)) (𝓝 (interiorFullBulk 0)) := by
  have he : puncturedInteriorBulk =ᶠ[𝓝[≠] (0:ℂ)] interiorFullBulk := by
    have hn0 : ∀ᶠ s : ℂ in 𝓝 (0:ℂ), ‖s‖ < 1 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds
        (by norm_num : ‖(0:ℂ)‖ < (1:ℝ))
    have hn : ∀ᶠ s : ℂ in 𝓝[≠] (0:ℂ), ‖s‖ < 1 :=
      hn0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hn, self_mem_nhdsWithin] with s hs hs0
    exact puncturedInteriorBulk_eq_existing hs0 hs
  have hc := (interiorFullBulk_analyticOn 0 (by norm_num)).continuousAt
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

/-- Unconditional identity of the constructed F001 and existing physical HT germs
on their entire common disk, including the formerly removable point s=0. -/
theorem interiorBulk_eqOn_existing :
    EqOn interiorBulk interiorFullBulk {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    change Function.update puncturedInteriorBulk 0
      (limUnder (𝓝[≠] (0:ℂ)) puncturedInteriorBulk) 0 = interiorFullBulk 0
    rw [Function.update_self]
    exact puncturedInteriorBulk_tendsto_zero.limUnder_eq
  · rw [interiorBulk_eq_punctured hs0]
    exact puncturedInteriorBulk_eq_existing hs0 hs

theorem interiorBulk_analyticOn :
    AnalyticOnNhd ℂ interiorBulk {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  apply (interiorFullBulk_analyticOn s hs).congr
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hs] with z hz
  exact (interiorBulk_eqOn_existing hz).symm

/-- Correct beta-inclusive new function, with no division at s=0. -/
def physicalSusceptibility (J : ℝ) (s : ℂ) : ℂ :=
  inverseTemperatureBranch J s * interiorBulk s

theorem physicalSusceptibility_real_eq_existing (J : ℝ) {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    physicalSusceptibility J (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ) := by
  rw [physicalSusceptibility, interiorBulk_eq_punctured
    (Complex.ofReal_ne_zero.mpr hx.ne'), puncturedInteriorBulk_real_eq_existing hx hx1]
  rfl

/-- Beta-inclusive equality follows from disk equality, never division by the
vanishing inverse-temperature factor at the origin. -/
theorem physicalSusceptibility_eqOn_existing (J : ℝ) :
    EqOn (physicalSusceptibility J) (interiorPhysicalSusceptibility J)
      {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  unfold physicalSusceptibility interiorPhysicalSusceptibility
  rw [interiorBulk_eqOn_existing hs]

theorem physicalSusceptibility_analyticOn {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (physicalSusceptibility J) {s : ℂ | ‖s‖ < 1} := by
  intro s hs
  exact (inverseTemperatureBranch_analyticAt_disk hJ hs).mul (interiorBulk_analyticOn s hs)

end
end IsingBulk.HT22.Physical

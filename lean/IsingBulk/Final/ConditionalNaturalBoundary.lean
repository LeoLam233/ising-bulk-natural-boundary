import IsingBulk.Final.UpperNoncancellation
import IsingBulk.Final.DenseBoundary
import IsingBulk.Final.PhysicalInputs
import IsingBulk.Tail.ExteriorSeries
import IsingBulk.First.ExteriorIdentitySymmetry

/-! Source thm:conditional, using the internally constructed whole-exterior
series. The actual absolute tail remains an explicit premise here; only a
separate theorem_tail may discharge it for the unconditional thm:nb. -/
namespace IsingBulk.Final
noncomputable section
open Filter Set IsingBulk.First IsingBulk.Tail
open scoped Topology

theorem sourceS_im_pos_of_upper_exterior {s : ℂ} (hs : 1 < ‖s‖) (hi : 0 < s.im) :
    0 < (sourceS s).im := by
  have hn : 1 < Complex.normSq s := Complex.one_lt_normSq_iff.mpr hs
  have h0 : Complex.normSq s ≠ 0 := by linarith
  have hform : (sourceS s).im = s.im*(Complex.normSq s-1)/Complex.normSq s := by
    simp only [sourceS,Complex.add_im,Complex.inv_im]
    field_simp
    ring
  rw [hform]
  exact div_pos (mul_pos hi (by linarith)) (by linarith)

theorem exteriorNormalizedBulk_symmetry :
    ∀ s : ℂ, 1 < ‖s‖ →
      exteriorNormalizedBulk (-s)=exteriorNormalizedBulk s ∧
      exteriorNormalizedBulk (star s)=star (exteriorNormalizedBulk s) := by
  apply exterior_symmetry_of_near_infinity exteriorNormalizedBulk exteriorNormalizedBulk_analyticOn
  · intro s hs
    rw [exteriorNormalizedBulk_eq_quarter_far (by simpa only [norm_neg] using hs),
      exteriorNormalizedBulk_eq_quarter_far hs,normalizedBulkSeries_even]
  · intro s hs
    rw [exteriorNormalizedBulk_eq_quarter_far (by simpa only [norm_star] using hs),
      exteriorNormalizedBulk_eq_quarter_far hs]
    exact normalizedBulkSeries_conjugate _ (by linarith)

theorem selected_exterior_nonextension_of_tail {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hab : a ≠ b) (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b))
    (hTail : ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j) :
    ¬ HasExteriorExtension exteriorNormalizedBulk (PrimeFamily.selectedPoint p a b) := by
  have hlocal := selected_bulk_nonextension_of_absolute_tail hp hp11 ha hb hab hTW hTail
  apply no_extension_of_eventuallyEq_exterior _ hlocal
  have hi : 0 < (PrimeFamily.selectedPoint p a b).im := by
    rw [PrimeFamily.selectedPoint,Complex.exp_ofReal_mul_I_im]
    exact (selectedOrderedChart ha hb).sin_theta_pos
  filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hi)] with s hs
  intro hse
  have hu := sourceS_im_pos_of_upper_exterior hse hs
  simp only [normalizedUpperBulk,exteriorNormalizedBulk,exteriorEvenSeries_eq_upper hu]

/-- The manuscript's conditional natural-boundary implication. Its conditional
premise is the literal all-j absolute higher-even tail for every selected point.
No root continuation, full-series holomorphy or noncancellation is external. -/
theorem theorem_conditional
    (hTW : ∀ p : ℕ, ∀ a b : ℤ, p.Prime → 11 ≤ p →
      PrimeFamily.Admissible p a → PrimeFamily.Admissible p b → a ≠ b →
      PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b))
    (hTail : ∀ p : ℕ, ∀ a b : ℤ, ∀ _hp : p.Prime, ∀ _hp11 : 11 ≤ p,
      ∀ ha : PrimeFamily.Admissible p a, ∀ hb : PrimeFamily.Admissible p b,
      a ≠ b → ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j) :
    ∀ z : ℂ, ‖z‖=1 → ¬ HasExteriorExtension exteriorNormalizedBulk z := by
  apply unit_circle_no_extension_of_selected
    (fun s hs => (exteriorNormalizedBulk_symmetry s hs).1)
    (fun s hs => (exteriorNormalizedBulk_symmetry s hs).2)
  rintro z ⟨p,a,b,hp,hp11,hab,ha,hb,rfl⟩
  exact selected_exterior_nonextension_of_tail hp hp11 ha hb hab
    (hTW p a b hp hp11 ha hb hab) (hTail p a b hp hp11 ha hb hab)

/-- E1 and E2 identify the real restriction of the internally constructed
exterior germ. They do not supply its complex convergence or analyticity. -/
theorem physical_exterior_germ_identification {X : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : RealFredholmE1 X M) (hE2 : YangMagnetizationE2 M) :
    AnalyticOnNhd ℂ exteriorNormalizedBulk exteriorDomain ∧
      ∀ x : ℝ, 16 < x → X (x:ℂ)=exteriorNormalizedBulk (x:ℂ) := by
  refine ⟨exteriorNormalizedBulk_analyticOn,?_⟩
  intro x hx
  rw [exteriorNormalizedBulk_eq_quarter_far (by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]; exact hx)]
  exact realNormalizedFredholmRepresentation_quarter X
    (normalized_real_representation_of_E1_E2 hE1 hE2) x hx

end
end IsingBulk.Final

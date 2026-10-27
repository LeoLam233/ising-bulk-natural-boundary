import IsingBulk.Preferred22.NaturalBoundary
import IsingBulk.Preferred22.Arithmetic
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! Proper analytic symmetry/factor-transfer logic adapted from the pinned repository,
with its density step replaced by the exact Preferred equal-angle prime family.
No previous natural-boundary conclusion or tail theorem is used. -/

/-! Local-extension obstructions transfer by the two proved source symmetries. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped Topology

theorem no_extension_neg_of_even {f : ℂ → ℂ} {z : ℂ}
    (heven : ∀ s : ℂ, 1 < ‖s‖ → f (-s)=f s)
    (hz : ¬ HasExteriorExtension f z) : ¬ HasExteriorExtension f (-z) := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  apply hz
  refine ⟨(fun s : ℂ => -s) ⁻¹' U,hU.preimage continuous_neg,by simpa using hzU,
    (fun s => g (-s)),?_,?_⟩
  · intro s hs
    exact (hg (-s) hs).comp analyticAt_id.neg
  · intro s hs
    dsimp only
    rw [heq ⟨hs.1,by simpa only [Set.mem_ofPred_eq,norm_neg] using hs.2⟩,heven s hs.2]

theorem analyticAt_conjugate_reflection {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g (star s)) : AnalyticAt ℂ (fun t => star (g (star t))) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(continuous_star.tendsto s).eventually hg.eventually_analyticAt] with t ht
  simpa only [Function.comp_def,star_star] using ht.differentiableAt.star_star

theorem no_extension_conjugate_of_real_symmetry {f : ℂ → ℂ} {z : ℂ}
    (hreal : ∀ s : ℂ, 1 < ‖s‖ → f (star s)=star (f s))
    (hz : ¬ HasExteriorExtension f z) : ¬ HasExteriorExtension f (star z) := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  apply hz
  refine ⟨star ⁻¹' U,hU.preimage continuous_star,hzU,
    (fun s => star (g (star s))),?_,?_⟩
  · intro s hs
    exact analyticAt_conjugate_reflection (hg (star s) hs)
  · intro s hs
    dsimp only
    rw [heq ⟨hs.1,by simpa only [Set.mem_ofPred_eq,norm_star] using hs.2⟩,hreal s hs.2,star_star]

end
end IsingBulk.Preferred22

/-! Local nonzero analytic factors preserve the natural-boundary obstruction.
This is local: it does not assert single-valued inverse-temperature branches
on the whole exterior. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped Topology

theorem extension_of_analytic_factor_extension {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0)
    (he : HasExteriorExtension (b*f) z) : HasExteriorExtension f z := by
  obtain ⟨U,hU,hzU,g,hg,hgf⟩ := he
  have hlocal : ∀ᶠ s in 𝓝 z, AnalyticAt ℂ b s ∧ b s ≠ 0 :=
    hb.eventually_analyticAt.and (hb.continuousAt.eventually_ne hb0)
  obtain ⟨V,hV,hVopen,hzV⟩ := mem_nhds_iff.mp hlocal
  refine ⟨U ∩ V,hU.inter hVopen,⟨hzU,hzV⟩,(fun s => g s / b s),?_,?_⟩
  · intro s hs
    exact (hg s hs.1).div (hV hs.2).1 (hV hs.2).2
  · intro s hs
    dsimp only
    rw [hgf ⟨hs.1.1,hs.2⟩]
    simp only [Pi.mul_apply]
    exact mul_div_cancel_left₀ (f s) (hV hs.1.2).2

theorem no_extension_mul_analytic_factor {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0) (hf : ¬ HasExteriorExtension f z) :
    ¬ HasExteriorExtension (b*f) z :=
  fun he => hf (extension_of_analytic_factor_extension hb hb0 he)

end
end IsingBulk.Preferred22

/-! The actual selected prime family and the two source symmetries obstruct
every unit point. Endpoint density is proved, not omitted. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter IsingBulk.PrimeFamily
open scoped Topology

def unitAngle (t : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I)

theorem unitAngle_continuous : Continuous unitAngle := by
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem unitAngle_conjugate (t : ℝ) : star (unitAngle t) = unitAngle (-t) := by
  unfold unitAngle
  rw [show star (Complex.exp ((t:ℂ)*Complex.I)) =
    Complex.exp (star ((t:ℂ)*Complex.I)) from (Complex.exp_conj _).symm]
  congr 1
  simp

theorem unitAngle_add_pi (t : ℝ) : unitAngle (t+Real.pi) = -unitAngle t := by
  unfold unitAngle
  rw [Complex.ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
  ring

theorem primeFamily_dense_closed_arc {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi/2) :
    unitAngle t ∈ closure primeRootFamily := by
  have hI : t ∈ closure (Ioo (0:ℝ) (Real.pi/2)) := by
    rw [closure_Ioo (by positivity : (0:ℝ) ≠ Real.pi/2)]
    exact ⟨ht,htpi⟩
  have hi := image_closure_subset_closure_image unitAngle_continuous (mem_image_of_mem unitAngle hI)
  apply (closure_minimal (s := unitAngle '' Ioo (0:ℝ) (Real.pi/2)) _ isClosed_closure) hi
  rintro _ ⟨a,ha,rfl⟩
  exact prime_root_family_dense_arc ha.1 ha.2

/-- Natural-boundary propagation is a theorem about actual open-neighborhood
extensions, and includes all four axis points via closed-arc density. -/
theorem unit_circle_no_extension_of_selected {f : ℂ → ℂ}
    (heven : ∀ s : ℂ, 1 < ‖s‖ → f (-s)=f s)
    (hreal : ∀ s : ℂ, 1 < ‖s‖ → f (star s)=star (f s))
    (hselected : ∀ z ∈ primeRootFamily, ¬ HasExteriorExtension f z) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension f z := by
  have hquarter (t : ℝ) (ht : 0 ≤ t) (htpi : t ≤ Real.pi/2) :
      ¬ HasExteriorExtension f (unitAngle t) :=
    no_extension_on_closure hselected (primeFamily_dense_closed_arc ht htpi)
  intro z hz
  have heq : unitAngle z.arg = z := by
    simpa only [hz,Complex.ofReal_one,one_mul,unitAngle] using Complex.norm_mul_exp_arg_mul_I z
  rw [← heq]
  by_cases hpos : 0 ≤ z.arg
  · by_cases hsmall : z.arg ≤ Real.pi/2
    · exact hquarter _ hpos hsmall
    · have ht : 0 ≤ Real.pi-z.arg := by linarith [Complex.arg_le_pi z]
      have htpi : Real.pi-z.arg ≤ Real.pi/2 := by linarith
      have h := no_extension_neg_of_even heven
        (no_extension_conjugate_of_real_symmetry hreal (hquarter _ ht htpi))
      rw [unitAngle_conjugate,show -(Real.pi-z.arg)=z.arg-Real.pi by ring] at h
      have hid : -unitAngle (z.arg-Real.pi)=unitAngle z.arg := by
        have ha := unitAngle_add_pi (z.arg-Real.pi)
        simpa only [sub_add_cancel] using ha.symm
      rwa [hid] at h
  · have hneg : z.arg ≤ 0 := le_of_not_ge hpos
    by_cases hsmall : -Real.pi/2 ≤ z.arg
    · have h := no_extension_conjugate_of_real_symmetry hreal
        (hquarter (-z.arg) (by linarith) (by linarith))
      simpa only [unitAngle_conjugate,neg_neg] using h
    · have ht : 0 ≤ z.arg+Real.pi := by linarith [Complex.neg_pi_lt_arg z]
      have htpi : z.arg+Real.pi ≤ Real.pi/2 := by linarith
      have h := no_extension_neg_of_even heven (hquarter _ ht htpi)
      simpa only [unitAngle_add_pi,neg_neg] using h

end
end IsingBulk.Preferred22

import IsingBulk.Preferred22.HorizontalFourier
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Exact periodic contour translation for the unconstrained angular site
integrals. This is a finite-dimensional Cauchy/Fubini identity. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators

theorem periodic_horizontal_translation (f : ℂ → ℂ) (h : ℝ) (hh : 0≤h)
    (hf : ∀ z : ℂ, |z.im|≤h → DifferentiableAt ℂ f z)
    (hp : Function.Periodic f (2*(Real.pi:ℂ))) (t : ℝ) (ht : |t|≤h) :
    (∫ x : ℝ in 0..2*Real.pi,f (x:ℂ)) =
      ∫ x : ℝ in 0..2*Real.pi,f ((x:ℂ)+(t:ℂ)*I) := by
  have hd : DifferentiableOn ℂ f
      (Set.uIcc (0:ℝ) (2*Real.pi) ×ℂ Set.uIcc (0:ℝ) t) := by
    intro z hz
    apply (hf z ?_).differentiableWithinAt
    have him : z.im ∈ Set.uIcc (0:ℝ) t := by simpa using hz.2
    have hleft : -h ≤ min 0 t := le_min (by linarith) ((abs_le.mp ht).1)
    have hright : max 0 t ≤ h := max_le hh ((abs_le.mp ht).2)
    exact abs_le.mpr ⟨hleft.trans him.1,him.2.trans hright⟩
  have he := integral_boundary_rect_eq_zero_of_differentiableOn f
    (0:ℂ) (2*(Real.pi:ℂ)+(t:ℂ)*I) (by simpa using hd)
  have hv : (fun y : ℝ => f (2*(Real.pi:ℂ)+(y:ℂ)*I))=
      fun y : ℝ => f ((y:ℂ)*I) := by
    funext y
    simpa only [add_comm] using hp ((y:ℂ)*I)
  norm_num at he
  rw [hv] at he
  exact sub_eq_zero.mp (by linear_combination he)

theorem multiAngleIntegral_integral_comm (n : ℕ)
    (f : ℝ × (Fin n → ℝ) → ℂ) (hf : Continuous f) :
    IsingBulk.First.multiAngleIntegral n
      (fun θ => ∫ u : ℝ in 0..2*Real.pi,f (u,θ)) =
      ∫ u : ℝ in 0..2*Real.pi,
        IsingBulk.First.multiAngleIntegral n (fun θ => f (u,θ)) := by
  have hc : Continuous (fun θ : Fin n → ℝ => ∫ u : ℝ in 0..2*Real.pi,f (u,θ)) :=
    IsingBulk.First.continuous_angle_integral (fun θ u => f (u,θ))
      (hf.comp continuous_swap)
  rw [IsingBulk.First.multiAngleIntegral_eq_box n _ hc]
  have hi : IntegrableOn f
      (Icc (0:ℝ) (2*Real.pi) ×ˢ IsingBulk.First.angleBox n) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have he := integral_integral_swap (μ := volume.restrict (Icc (0:ℝ) (2*Real.pi)))
    (ν := volume.restrict (IsingBulk.First.angleBox n))
    (f := fun u θ => f (u,θ)) (by simpa only [IntegrableOn,Function.uncurry_def,Measure.prod_restrict] using hi)
  have hleft : (fun θ : Fin n → ℝ => ∫ u : ℝ in 0..2*Real.pi,f (u,θ))=
      fun θ : Fin n → ℝ => ∫ u in Icc (0:ℝ) (2*Real.pi),f (u,θ) := by
    funext θ
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,integral_Icc_eq_integral_Ioc]
  rw [hleft,← he,intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u _
  exact (IsingBulk.First.multiAngleIntegral_eq_box n _
    (hf.comp (continuous_const.prodMk continuous_id))).symm

def ComplexCoordinatePeriodic (N : ℕ) (F : (Fin N → ℂ) → ℂ) : Prop :=
  ∀ w i,F (Function.update w i (w i+2*(Real.pi:ℂ)))=F w

theorem multiAngleIntegral_complex_translation (N : ℕ) (h : ℝ) (hh : 0≤h)
    (F : (Fin N → ℂ) → ℂ)
    (hF : ∀ w : Fin N → ℂ,(∀ i,|(w i).im|≤h) → AnalyticAt ℂ F w)
    (hp : ComplexCoordinatePeriodic N F) (t : Fin N → ℝ) (ht : ∀ i,|t i|≤h) :
    IsingBulk.First.multiAngleIntegral N (fun θ => F (fun i => (θ i:ℂ))) =
      IsingBulk.First.multiAngleIntegral N
        (fun θ => F (fun i => (θ i:ℂ)+(t i:ℂ)*I)) := by
  induction N with
  | zero =>
    simp only [IsingBulk.First.multiAngleIntegral]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let f₀ : ℝ × (Fin n → ℝ) → ℂ :=
      fun p => F (Fin.cons (p.1:ℂ) (fun i => (p.2 i:ℂ)))
    let f₁ : ℝ × (Fin n → ℝ) → ℂ :=
      fun p => F (Fin.cons (p.1:ℂ) (fun i => (p.2 i:ℂ)+(t i.succ:ℂ)*I))
    have hc₀ : Continuous f₀ := by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact ((hF _ (by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simpa using hh)).continuousAt.comp
        (by fun_prop))
    have hc₁ : Continuous f₁ := by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact ((hF _ (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hh
        · simpa using ht j.succ)).continuousAt.comp (by fun_prop))
    have hih (u : ℝ) :
        IsingBulk.First.multiAngleIntegral n (fun θ => f₀ (u,θ))=
        IsingBulk.First.multiAngleIntegral n (fun θ => f₁ (u,θ)) := by
      apply ih (fun w => F (Fin.cons (u:ℂ) w))
      · intro w hw
        exact (hF _ (by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hh
          · exact hw j)).comp (by
            apply analyticAt_pi_iff.mpr
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact analyticAt_const
            · exact (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt w)
      · intro w i
        have he : Fin.cons (u:ℂ) (Function.update w i (w i+2*(Real.pi:ℂ)))=
            Function.update (Fin.cons (u:ℂ) w : Fin (n+1) → ℂ) i.succ (w i+2*(Real.pi:ℂ)) := by
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
          · by_cases hk : k=i
            · subst k; simp
            · simp [Fin.succ_inj,hk]
        dsimp only
        rw [he]
        exact hp _ _
      · exact fun i => ht i.succ
    have hhead (θ : Fin n → ℝ) :
        (∫ u : ℝ in 0..2*Real.pi,f₁ (u,θ))=
          ∫ u : ℝ in 0..2*Real.pi,
            F (fun i => ((Fin.cons u θ : Fin (n+1) → ℝ) i:ℂ)+(t i:ℂ)*I) := by
      let w : Fin n → ℂ := fun i => (θ i:ℂ)+(t i.succ:ℂ)*I
      have hfd : ∀ z : ℂ,|z.im|≤h → DifferentiableAt ℂ (fun z => F (Fin.cons z w)) z := by
        intro z hz
        exact ((hF _ (by
          intro i
          refine Fin.cases hz (fun j => ?_) i
          simpa [w] using ht j.succ)).comp (by
            apply analyticAt_pi_iff.mpr
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · exact analyticAt_id
            · exact analyticAt_const)).differentiableAt
      have hfp : Function.Periodic (fun z => F (Fin.cons z w)) (2*(Real.pi:ℂ)) := by
        intro z
        have he : Function.update (Fin.cons z w : Fin (n+1) → ℂ) 0 (z+2*(Real.pi:ℂ))=
            (Fin.cons (z+2*(Real.pi:ℂ)) w : Fin (n+1) → ℂ) := by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        simpa only [Fin.cons_zero,he] using hp (Fin.cons z w) 0
      calc
        (∫ u : ℝ in 0..2*Real.pi,f₁ (u,θ)) =
            ∫ u : ℝ in 0..2*Real.pi,F (Fin.cons ((u:ℂ)+(t 0:ℂ)*I) w) :=
          periodic_horizontal_translation (fun z => F (Fin.cons z w)) h hh hfd hfp (t 0) (ht 0)
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro u _
          change F (Fin.cons ((u:ℂ)+(t 0:ℂ)*I) w)=
            F (fun i => ((Fin.cons u θ : Fin (n+1) → ℝ) i:ℂ)+(t i:ℂ)*I)
          apply congrArg F
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
    have he₀ (u : ℝ) (θ : Fin n → ℝ) :
        F (fun i => ((Fin.cons u θ : Fin (n+1) → ℝ) i:ℂ))=f₀ (u,θ) := by
      apply congrArg F
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [IsingBulk.First.multiAngleIntegral,he₀]
    rw [multiAngleIntegral_integral_comm n f₀ hc₀]
    simp_rw [hih]
    rw [← multiAngleIntegral_integral_comm n f₁ hc₁]
    congr 1
    funext θ
    exact hhead θ

end
end IsingBulk.Preferred22

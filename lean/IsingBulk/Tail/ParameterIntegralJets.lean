import IsingBulk.Tail.CompactSmoothDivision

/-! Exact finite directional jets through a fixed parameter integral.
Quantitative bounds come from the supplied jets, not compactness in the dimension. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped ContDiff
universe u
variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
variable {ι : Type*}

def parameterWordJet (d : ι → E) : List ι → (E → G) → E → G
  | [], f => f
  | i :: l, f => fun x => fderiv ℝ (parameterWordJet d l f) x (d i)

def jointParameterWordJet (d : ι → E) : List ι → (E × ℝ → G) → E × ℝ → G
  | [], F => F
  | i :: l, F => fun p => compactParameterDerivative (jointParameterWordJet d l F) p (d i)

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
lemma jointParameterWordJet_contDiff (d : ι → E) (l : List ι)
    (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jointParameterWordJet d l F) := by
  induction l with
  | nil => exact hF
  | cons i l ih =>
    exact (compactParameterDerivative_contDiff _ ih).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] [CompleteSpace G] in
lemma jointParameterWordJet_slice (d : ι → E) (l : List ι)
    (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) (x : E) (t : ℝ) :
    jointParameterWordJet d l F (x,t) = parameterWordJet d l (fun y => F (y,t)) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have he : (fun y => jointParameterWordJet d l F (y,t)) =
        parameterWordJet d l (fun y => F (y,t)) := funext ih
    have hd := (compactParameterDerivative_hasFDerivAt _
      (jointParameterWordJet_contDiff d l F hF) x t).fderiv
    rw [he] at hd
    change _ = (fderiv ℝ _ x) (d i)
    rw [hd]
    rfl

omit [CompleteSpace G] in
theorem parameter_word_jet_integral (d : ι → E) (l : List ι)
    (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) (x : E) :
    parameterWordJet d l (fun y => ∫ t in (0:ℝ)..1, F (y,t)) x =
      ∫ t in (0:ℝ)..1, parameterWordJet d l (fun y => F (y,t)) x := by
  have hcore : ∀ l : List ι,
      parameterWordJet d l (fun y => ∫ t in (0:ℝ)..1, F (y,t)) =
      fun y => ∫ t in (0:ℝ)..1, jointParameterWordJet d l F (y,t) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      funext y
      change fderiv ℝ _ y (d i) = _
      rw [ih, (compact_parameter_integral_hasFDerivAt _
        (jointParameterWordJet_contDiff d l F hF) y).fderiv]
      exact ContinuousLinearMap.intervalIntegral_apply
        (((compactParameterDerivative_contDiff _
          (jointParameterWordJet_contDiff d l F hF)).continuous.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1) (d i)
  rw [hcore l]
  apply intervalIntegral.integral_congr
  intro t ht
  exact jointParameterWordJet_slice d l F hF x t

omit [CompleteSpace G] in
theorem parameter_word_jet_integral_norm_le (d : ι → E) (l : List ι)
    (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) (x : E) (B : ℝ)
    (hB : ∀ t ∈ Icc (0:ℝ) 1,
      ‖parameterWordJet d l (fun y => F (y,t)) x‖ ≤ B) :
    ‖parameterWordJet d l (fun y => ∫ t in (0:ℝ)..1, F (y,t)) x‖ ≤ B := by
  rw [parameter_word_jet_integral d l F hF x]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := B) (f := fun t =>
      parameterWordJet d l (fun y => F (y,t)) x)
    (fun t ht => hB t (by simpa using (uIoc_subset_uIcc ht)))
  simpa using hb

end
end IsingBulk.Tail

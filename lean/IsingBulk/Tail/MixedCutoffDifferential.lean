import IsingBulk.Tail.MixedDensityLieGerm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem fderiv_mixedFreeze_basis {N : ℕ} (S : Finset (Fin N)) (background x : Fin N → ℝ)
    (w : (Fin N → ℝ) → ℝ) (hw : DifferentiableAt ℝ w (mixedFreeze S background x)) (i : Fin N) :
    fderiv ℝ (fun a => w (mixedFreeze S background a)) x (Pi.single i 1)=
      if i∈S then fderiv ℝ w (mixedFreeze S background x) (Pi.single i 1) else 0 := by
  have hfz := (mixedFreeze_contDiff S background).differentiable (by simp) x
  have hh := (hw.comp x hfz).hasFDerivAt.comp_hasDerivAt_of_eq (x i)
    (hasDerivAt_update x i (x i)) (by simp only [Function.update_eq_self])
  have hh' : HasDerivAt (fun u => w (mixedFreeze S background (Function.update x i u)))
      (fderiv ℝ (fun a => w (mixedFreeze S background a)) x (Pi.single i 1)) (x i) := hh
  by_cases hi : i∈S
  · rw [ite_eq_left hi]
    have hxi : mixedFreeze S background x i=x i := by simp [mixedFreeze,hi]
    have hh₂ := hw.hasFDerivAt.comp_hasDerivAt_of_eq (x i)
      (hasDerivAt_update (mixedFreeze S background x) i (x i)) (by rw [← hxi,Function.update_eq_self])
    simp only [mixedFreeze_update_active S background x i hi] at hh'
    exact hh'.unique hh₂
  · rw [ite_eq_right hi]
    simp only [mixedFreeze_update_inactive S background x i hi] at hh'
    exact hh'.unique (hasDerivAt_const (x i) _)

theorem mixed_cutoff_transport {n : ℕ} (S : Finset (Fin (n+1))) (background x : Fin (n+1) → ℝ)
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ) (s : ℂ)
    (hV : ∀ i,i∉S → V s (mixedFreeze S background x) i=0)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : DifferentiableAt ℝ w (mixedFreeze S background x)) :
    (∑ i,V s (mixedFreeze S background x) i*
      (fderiv ℝ (fun a => w (mixedFreeze S background a)) x (Pi.single i 1):ℂ))=
    ∑ i,V s (mixedFreeze S background x) i*(fderiv ℝ w (mixedFreeze S background x) (Pi.single i 1):ℂ) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_mixedFreeze_basis S background x w hw i]
  by_cases hi : i∈S
  · simp only [hi,ite_true]
  · simp [hi,hV i hi]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedRegularDensityStep_analytic (e₀ e₁ e₂ : E) (R₁ R₂ F : E → ℂ) (x : E)
    (hR₁ : AnalyticAt ℂ R₁ x) (hR₂ : AnalyticAt ℂ R₂ x) (hF : AnalyticAt ℂ F x) :
    AnalyticAt ℂ (mixedRegularDensityStep e₀ e₁ e₂ R₁ R₂ F) x := by
  have hD (G : E → ℂ) (hG : AnalyticAt ℂ G x) (e : E) :
      AnalyticAt ℂ (fun z => fderiv ℂ G z e) x :=
    ((ContinuousLinearMap.apply ℂ ℂ e).analyticAt _).comp hG.fderiv
  exact (((hD F hF e₀).add (hR₁.mul (hD F hF e₁))).add (hR₂.mul (hD F hF e₂))).add
    (((hD R₁ hR₁ e₁).add (hD R₂ hR₂ e₂)).mul hF)

theorem MixedDensityJetTerm.child_analytic {N : ℕ} (T : MixedDensityJetTerm N E)
    (e₀ e₁ e₂ : E) (R₁ R₂ : E → ℂ) (V : Fin N → E → ℂ) (x : E)
    (hR₁ : AnalyticAt ℂ R₁ x) (hR₂ : AnalyticAt ℂ R₂ x)
    (hV : ∀ i,AnalyticAt ℂ (V i) x) (hT : AnalyticAt ℂ T.regularPart x) (a : Option (Fin N)) :
    AnalyticAt ℂ (T.child e₀ e₁ e₂ R₁ R₂ V a).regularPart x := by
  cases a with
  | none => exact mixedRegularDensityStep_analytic e₀ e₁ e₂ R₁ R₂ T.regularPart x hR₁ hR₂ hT
  | some i => exact (hV i).neg.mul hT

theorem mixedDensityJetTerms_analytic {N : ℕ} (e₀ e₁ e₂ : E) (R₁ R₂ F : E → ℂ)
    (V : Fin N → E → ℂ) (x : E) (hR₁ : AnalyticAt ℂ R₁ x) (hR₂ : AnalyticAt ℂ R₂ x)
    (hV : ∀ i,AnalyticAt ℂ (V i) x) (hF : AnalyticAt ℂ F x) (k : ℕ) :
    ∀ T∈mixedDensityJetTerms e₀ e₁ e₂ R₁ R₂ F V k,AnalyticAt ℂ T.regularPart x := by
  induction k with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [mixedDensityJetTerms,List.mem_singleton] using hT
    subst T
    exact hF
  | succ k ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    exact P.child_analytic e₀ e₁ e₂ R₁ R₂ V x hR₁ hR₂ hV (ih P hP) a

end
end IsingBulk.Tail

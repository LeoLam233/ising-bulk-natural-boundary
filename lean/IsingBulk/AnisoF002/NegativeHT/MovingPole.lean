import IsingBulk.AnisoF002.NegativeHT.LocalSpectralPhase
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local moving pole of the genuine negative-HT phase sum

The phase branch is constructed from cosh in `LocalSpectralPhase`.
This file applies the analytic inverse theorem to its full n-angle phase
sum and proves local existence and uniqueness of the moving pole.  The
neighborhoods proved here may depend on n.  Uniform radii, higher-order
pole errors, the physical residue, and global branch matching are still
required by F002's quantitative real-cycle argument.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Analytic scalar implicit construction, proved from a block-triangular
inverse map.  The nonzero scalar partial derivative is the sole condition. -/
theorem exists_analytic_scalar_implicit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (F : E × ℂ → ℂ) (p : E × ℂ) (L : (E × ℂ) →L[ℂ] ℂ)
    (hF : AnalyticAt ℂ F p) (hL : HasFDerivAt F L p) (hD : L (0,1) ≠ 0) :
    ∃ T : E → ℂ, AnalyticAt ℂ T p.1 ∧ T p.1=p.2 ∧
      (∀ᶠ x in 𝓝 p.1, F (x,T x)=F p) ∧
      ∀ᶠ a in 𝓝 p, F a=F p ↔ T a.1=a.2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let Ψ : E × ℂ → E × ℂ := fun a => (a.1,F a)
  let M : (E × ℂ) →L[ℂ] (E × ℂ) := (ContinuousLinearMap.fst ℂ E ℂ).prod L
  have hsplit : ∀ a : E × ℂ, L a = L (a.1,0)+a.2*L (0,1) := by
    intro a
    have he : a = (a.1,0)+a.2 • ((0:E),(1:ℂ)) := by ext <;> simp
    rw [he, map_add, map_smul]
    simp
  have hbij : Function.Bijective M := by
    constructor
    · intro a b hab
      have hf := congrArg Prod.fst hab
      have hl := congrArg Prod.snd hab
      change a.1=b.1 at hf
      change L a=L b at hl
      apply Prod.ext hf
      rw [hsplit a, hsplit b, hf] at hl
      exact (mul_right_cancel₀ hD (add_left_cancel hl))
    · intro b
      refine ⟨(b.1,(b.2-L (b.1,0))/L (0,1)), ?_⟩
      apply Prod.ext
      · rfl
      · change L (b.1,(b.2-L (b.1,0))/L (0,1))=b.2
        rw [hsplit]
        simp only
        rw [div_mul_cancel₀ _ hD]
        ring
  let e : (E × ℂ) ≃L[ℂ] (E × ℂ) :=
    (LinearEquiv.ofBijective M.toLinearMap hbij).toContinuousLinearEquiv
  have hfstrict : HasStrictFDerivAt F L p := by
    rw [← hL.fderiv]
    exact hF.hasStrictFDerivAt
  have hs : HasStrictFDerivAt Ψ (e : (E × ℂ) →L[ℂ] (E × ℂ)) p :=
    (ContinuousLinearMap.fst ℂ E ℂ).hasStrictFDerivAt.prodMk hfstrict
  have ha : AnalyticAt ℂ Ψ p := analyticAt_fst.prod hF
  let H := hs.toOpenPartialHomeomorph Ψ
  have hm : p ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have hi : AnalyticAt ℂ H.symm (p.1,F p) :=
    H.analyticAt_symm' hm ha hs.hasFDerivAt.fderiv
  let T : E → ℂ := fun x => (H.symm (x,F p)).2
  have hTa : AnalyticAt ℂ T p.1 :=
    analyticAt_snd.comp (hi.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl)
  have hTv : T p.1=p.2 := congrArg Prod.snd (H.left_inv hm)
  have hright : ∀ᶠ x in 𝓝 p.1, Ψ (H.symm (x,F p))=(x,F p) :=
    (continuousAt_id.prodMk continuousAt_const).eventually (H.eventually_right_inverse' hm)
  have hzero : ∀ᶠ x in 𝓝 p.1, F (x,T x)=F p := by
    filter_upwards [hright] with x hx
    have hx1 : (H.symm (x,F p)).1=x := congrArg Prod.fst hx
    have hx2 : F (H.symm (x,F p))=F p := congrArg Prod.snd hx
    have hp : H.symm (x,F p)=(x,T x) := Prod.ext hx1 rfl
    rwa [hp] at hx2
  refine ⟨T,hTa,hTv,hzero,?_⟩
  have hleft : ∀ᶠ a in 𝓝 p, H.symm (Ψ a)=a := H.eventually_left_inverse hm
  have hproj : ∀ᶠ a in 𝓝 p, F (a.1,T a.1)=F p :=
    continuousAt_fst.eventually hzero
  filter_upwards [hleft,hproj] with a ha hp
  constructor
  · intro hf
    have he : T a.1=a.2 := by
      change (H.symm (a.1,F p)).2=a.2
      rw [← hf]
      exact congrArg Prod.snd ha
    exact he
  · intro ht
    simpa only [ht] using hp

/-- The complete phase sum in independent displacement coordinates. -/
def negativePhaseSum (n : ℕ) (g : ℂ × ℂ → ℂ) (d : ℝ)
    (a : (Fin n → ℂ) × ℂ) : ℂ :=
  ∑ i : Fin n, g (a.2,(d:ℂ)+a.1 i)

def angleSum (n : ℕ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ i : Fin n, ContinuousLinearMap.proj i

theorem angleSum_apply (n : ℕ) (v : Fin n → ℂ) : angleSum n v=∑ i, v i := by
  simp [angleSum]

def phaseSumDerivative (n : ℕ) (c : ℂ) (d : ℝ) :
    ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ :=
  c • ((n:ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ -
    (Real.sin d : ℂ) • ((angleSum n).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)))

theorem phaseSumDerivative_apply (n : ℕ) (c : ℂ) (d : ℝ)
    (a : (Fin n → ℂ) × ℂ) :
    phaseSumDerivative n c d a = c*((n:ℂ)*a.2-(Real.sin d : ℂ)*∑ i, a.1 i) := by
  simp [phaseSumDerivative, angleSum_apply]

theorem negativePhaseSum_analyticAt (n : ℕ) (g : ℂ × ℂ → ℂ) (d : ℝ) (τ : ℂ)
    (hg : AnalyticAt ℂ g (τ,(d:ℂ))) :
    AnalyticAt ℂ (negativePhaseSum n g d) ((0:Fin n → ℂ),τ) := by
  apply Finset.analyticAt_fun_sum
  intro i _
  let v : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)
  have hi : AnalyticAt ℂ (fun a : (Fin n → ℂ) × ℂ => (a.2,(d:ℂ)+a.1 i)) (0,τ) :=
    analyticAt_snd.prod (analyticAt_const.add (v.analyticAt _))
  exact hg.comp_of_eq hi (by simp)

theorem negativePhaseSum_hasFDerivAt (n : ℕ) (g : ℂ × ℂ → ℂ) (d : ℝ) (τ c : ℂ)
    (hg : HasFDerivAt g
      (c • ContinuousLinearMap.fst ℂ ℂ ℂ -
        (c*(Real.sin d:ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ) (τ,(d:ℂ))) :
    HasFDerivAt (negativePhaseSum n g d) (phaseSumDerivative n c d)
      ((0:Fin n → ℂ),τ) := by
  let v (i : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)
  let t : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
  have hi : ∀ i : Fin n,
      HasFDerivAt (fun a : (Fin n → ℂ) × ℂ => g (a.2,(d:ℂ)+a.1 i))
        ((c • ContinuousLinearMap.fst ℂ ℂ ℂ -
          (c*(Real.sin d:ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ).comp (t.prod (v i))) (0,τ) := by
    intro i
    have hh : HasFDerivAt (fun a : (Fin n → ℂ) × ℂ => (a.2,(d:ℂ)+a.1 i))
        (t.prod (v i)) (0,τ) :=
      t.hasFDerivAt.prodMk ((v i).hasFDerivAt.const_add (d:ℂ))
    have hgi : HasFDerivAt g
        (c • ContinuousLinearMap.fst ℂ ℂ ℂ -
          (c*(Real.sin d:ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ)
        ((0,τ).2,(d:ℂ)+(0:Fin n → ℂ) i) := by simpa using hg
    exact hgi.comp (0,τ) hh
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  convert hs using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro a
    simp [phaseSumDerivative_apply, v, t, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

/-- A locally unique analytic pole of the actual constructed phase sum.
This statement has no supplied pole or assumed inverse branch. -/
theorem exists_local_moving_pole (n : ℕ) (B : ℂ → ℂ) (φ d : ℝ)
    (hn : 0<n) (hφ : Real.sin φ ≠ 0)
    (hB : AnalyticAt ℂ B ((1-Real.cos d : ℝ):ℂ))
    (hB0 : B ((1-Real.cos d : ℝ):ℂ) ≠ 0) :
    ∃ g : ℂ × ℂ → ℂ, ∃ T : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ g ((1-Real.cos d : ℝ),(d:ℂ)) ∧
      g ((1-Real.cos d : ℝ),(d:ℂ))=(φ:ℂ)*Complex.I ∧
      (∀ᶠ a in 𝓝 ((1-Real.cos d : ℝ),(d:ℂ)),
        Complex.cosh (g a)=localNegativeDispersion B φ a) ∧
      AnalyticAt ℂ T 0 ∧ T 0=((1-Real.cos d : ℝ):ℂ) ∧
      (∀ᶠ v in 𝓝 (0:Fin n → ℂ), ∑ i, g (T v,(d:ℂ)+v i)=(n:ℂ)*((φ:ℂ)*Complex.I)) ∧
      ∀ᶠ a in 𝓝 ((0:Fin n → ℂ),((1-Real.cos d : ℝ):ℂ)),
        (∑ i, g (a.2,(d:ℂ)+a.1 i)=(n:ℂ)*((φ:ℂ)*Complex.I)) ↔ T a.1=a.2 := by
  obtain ⟨g,hga,hgv,hgd,hge⟩ := exists_local_negative_phase B φ d hφ hB
  let τ : ℂ := ((1-Real.cos d : ℝ):ℂ)
  let c : ℂ := ((Real.sin φ:ℂ)*Complex.I)⁻¹*B τ
  have hc : c ≠ 0 := by
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hφ) Complex.I_ne_zero)) hB0
  have hder := negativePhaseSum_hasFDerivAt n g d τ c hgd
  have ha := negativePhaseSum_analyticAt n g d τ hga
  have hD : phaseSumDerivative n c d (0,1) ≠ 0 := by
    simpa only [phaseSumDerivative_apply, Pi.zero_apply, Finset.sum_const_zero,
      mul_one, mul_zero, sub_zero] using mul_ne_zero hc
        (show (n:ℂ)≠0 by exact_mod_cast hn.ne')
  obtain ⟨T,hTa,hTv,hzero,hunique⟩ := exists_analytic_scalar_implicit
    (negativePhaseSum n g d) (0,τ) (phaseSumDerivative n c d) ha hder hD
  have hval : negativePhaseSum n g d (0,τ)=(n:ℂ)*((φ:ℂ)*Complex.I) := by
    have hv : g (τ,(d:ℂ))=(φ:ℂ)*Complex.I := hgv
    simp only [negativePhaseSum, Pi.zero_apply, add_zero, hv, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hval] at hzero hunique
  refine ⟨g,T,hga,hgv,hge,hTa,hTv,?_,?_⟩
  · simpa only [negativePhaseSum] using hzero
  · simpa only [negativePhaseSum] using hunique

end

end IsingBulk.AnisoF002.NegativeHT

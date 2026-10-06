import IsingBulk.Analysis.LieIntegration
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Real-smooth angular variables and holomorphic parameter differentiation.
No analytic extension of any real angular cutoff is used. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ParameterSmoothOn (Ω : Set (ℂ × E)) (F : ℂ → E → ℂ) : Prop :=
  ∀ p∈Ω,ContDiffAt ℝ ∞ (Function.uncurry F) p ∧ DifferentiableAt ℂ (fun s => F s p.2) p.1

def realDirection (A : (ℂ × E) → ℂ) (v : ℂ × E) (p : ℂ × E) : ℂ := fderiv ℝ A p v

theorem parameterSlice_fderiv (A : (ℂ × E) → ℂ) (p : ℂ × E)
    (hA : DifferentiableAt ℝ A p) (v : ℂ) :
    fderiv ℝ (fun z => A (z,p.2)) p.1 v=fderiv ℝ A p (v,0) := by
  have hh := (hA.hasFDerivAt.comp p.1
    ((hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1))).fderiv
  exact congrArg (fun L => L v) hh

theorem angularSlice_fderiv (A : (ℂ × E) → ℂ) (p : ℂ × E)
    (hA : DifferentiableAt ℝ A p) (v : E) :
    fderiv ℝ (fun y => A (p.1,y)) p.2 v=fderiv ℝ A p (0,v) := by
  have hh := (hA.hasFDerivAt.comp p.2
    ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))).fderiv
  exact congrArg (fun L => L v) hh

theorem parameter_CR (A : (ℂ × E) → ℂ) (p : ℂ × E)
    (hA : DifferentiableAt ℝ A p) (hC : DifferentiableAt ℂ (fun z => A (z,p.2)) p.1) :
    fderiv ℝ A p (Complex.I,0)=Complex.I • fderiv ℝ A p (1,0) := by
  have hh := (differentiableAt_complex_iff_differentiableAt_real.mp hC).2
  simpa only [parameterSlice_fderiv A p hA] using hh

theorem realDirection_contDiffAt {A : (ℂ × E) → ℂ} {p : ℂ × E}
    (hA : ContDiffAt ℝ ∞ A p) (v : ℂ × E) : ContDiffAt ℝ ∞ (realDirection A v) p := by
  exact (hA.fderiv_right (by simp) : ContDiffAt ℝ ∞ (fderiv ℝ A) p).clm_apply contDiffAt_const

theorem realDirection_fderiv {A : (ℂ × E) → ℂ} {p : ℂ × E}
    (hA : ContDiffAt ℝ ∞ A p) (v w : ℂ × E) :
    fderiv ℝ (realDirection A v) p w=fderiv ℝ (fderiv ℝ A) p w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ A) p :=
    (hA.fderiv_right (by simp) : ContDiffAt ℝ ∞ (fderiv ℝ A) p).differentiableAt (by simp)
  unfold realDirection
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem parameterSmooth_direction {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) (v : ℂ × E) :
    ParameterSmoothOn Ω (fun s y => realDirection (Function.uncurry F) v (s,y)) := by
  intro p hp
  let A := Function.uncurry F
  have hA : ContDiffAt ℝ ∞ A p := (hF p hp).1
  have hD := realDirection_contDiffAt hA v
  refine ⟨hD,differentiableAt_complex_iff_differentiableAt_real.mpr ⟨?_,?_⟩⟩
  · exact hD.differentiableAt (by simp) |>.comp p.1
      ((differentiableAt_id.prodMk (differentiableAt_const p.2)) : DifferentiableAt ℝ (fun z => (z,p.2)) p.1)
  · have he : realDirection A (Complex.I,0) =ᶠ[𝓝 p] (fun z => Complex.I • realDirection A (1,0) z) := by
      filter_upwards [hΩ.mem_nhds hp] with z hz
      exact parameter_CR A z ((hF z hz).1.differentiableAt (by simp)) (hF z hz).2
    have hd1 := (realDirection_contDiffAt hA (1,0)).differentiableAt (by simp)
    have hder := he.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const_smul hd1] at hder
    have hderv := congrArg (fun L => L v) hder
    simp only [smul_apply] at hderv
    rw [realDirection_fderiv hA,realDirection_fderiv hA] at hderv
    have hsym := hA.isSymmSndFDerivAt (by simp)
    rw [parameterSlice_fderiv _ p (hD.differentiableAt (by simp)),
      parameterSlice_fderiv _ p (hD.differentiableAt (by simp)),
      realDirection_fderiv hA,realDirection_fderiv hA]
    rw [hsym (Complex.I,0) v,hsym (1,0) v]
    exact hderv


theorem ParameterSmoothOn.congr {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F G : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F)
    (he : ∀ p∈Ω,G p.1 p.2=F p.1 p.2) : ParameterSmoothOn Ω G := by
  intro p hp
  have hfull : Function.uncurry G =ᶠ[𝓝 p] Function.uncurry F := by
    filter_upwards [hΩ.mem_nhds hp] with z hz
    exact he z hz
  have hslice : (fun s => G s p.2) =ᶠ[𝓝 p.1] (fun s => F s p.2) := by
    have hc : ContinuousAt (fun s : ℂ => (s,p.2)) p.1 := by fun_prop
    filter_upwards [hc.preimage_mem_nhds (hΩ.mem_nhds hp)] with s hs
    exact he (s,p.2) hs
  exact ⟨(hF p hp).1.congr_of_eventuallyEq hfull,(hF p hp).2.congr_of_eventuallyEq hslice⟩

theorem ParameterSmoothOn.paramDeriv {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) :
    ParameterSmoothOn Ω (fun s y => deriv (fun z => F z y) s) := by
  apply (parameterSmooth_direction hΩ hF (1,0)).congr hΩ
  intro p hp
  have hCR := differentiableAt_complex_iff_differentiableAt_real.mp (hF p hp).2
  rw [complexOfReal_deriv hCR.1 hCR.2]
  exact parameterSlice_fderiv (Function.uncurry F) p ((hF p hp).1.differentiableAt (by simp)) 1

theorem ParameterSmoothOn.angularDirection {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) (v : E) :
    ParameterSmoothOn Ω (fun s y => fderiv ℝ (F s) y v) := by
  apply (parameterSmooth_direction hΩ hF (0,v)).congr hΩ
  intro p hp
  exact angularSlice_fderiv (Function.uncurry F) p ((hF p hp).1.differentiableAt (by simp)) v

theorem ParameterSmoothOn.mul {Ω : Set (ℂ × E)} {F G : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (hG : ParameterSmoothOn Ω G) :
    ParameterSmoothOn Ω (fun s y => F s y*G s y) := by
  intro p hp
  exact ⟨(hF p hp).1.mul (hG p hp).1,(hF p hp).2.mul (hG p hp).2⟩

theorem ParameterSmoothOn.sub {Ω : Set (ℂ × E)} {F G : ℂ → E → ℂ}
    (hF : ParameterSmoothOn Ω F) (hG : ParameterSmoothOn Ω G) :
    ParameterSmoothOn Ω (fun s y => F s y-G s y) := by
  intro p hp
  exact ⟨(hF p hp).1.sub (hG p hp).1,(hF p hp).2.sub (hG p hp).2⟩

theorem ParameterSmoothOn.sum {Ω : Set (ℂ × E)} {ι : Type*} (S : Finset ι)
    (F : ι → ℂ → E → ℂ) (hF : ∀ i∈S,ParameterSmoothOn Ω (F i)) :
    ParameterSmoothOn Ω (fun s y => ∑ i∈S,F i s y) := by
  intro p hp
  exact ⟨ContDiffAt.sum (fun i hi => (hF i hi p hp).1),
    DifferentiableAt.fun_sum (fun i hi => (hF i hi p hp).2)⟩

theorem ParameterSmoothOn.lieStep {n : ℕ} {Ω : Set (ℂ × IsingBulk.Lie.AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → IsingBulk.Lie.AngularSpace n → Fin (n+1) → ℂ)
    (F : ℂ → IsingBulk.Lie.AngularSpace n → ℂ)
    (hV : ∀ i,ParameterSmoothOn Ω (fun s y => V s y i)) (hF : ParameterSmoothOn Ω F) :
    ParameterSmoothOn Ω (IsingBulk.Lie.lieStep V F) := by
  exact (hF.paramDeriv hΩ).sub (ParameterSmoothOn.sum Finset.univ _
    (fun i _ => ((hV i).mul hF).angularDirection hΩ (Pi.single i 1)))

theorem ParameterSmoothOn.iterate_lieStep {n : ℕ} {Ω : Set (ℂ × IsingBulk.Lie.AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → IsingBulk.Lie.AngularSpace n → Fin (n+1) → ℂ)
    (F : ℂ → IsingBulk.Lie.AngularSpace n → ℂ)
    (hV : ∀ i,ParameterSmoothOn Ω (fun s y => V s y i)) (hF : ParameterSmoothOn Ω F) (k : ℕ) :
    ParameterSmoothOn Ω ((IsingBulk.Lie.lieStep V)^[k] F) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.lieStep hΩ V _ hV

end
end IsingBulk.Tail

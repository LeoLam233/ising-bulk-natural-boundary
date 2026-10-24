import IsingBulk.Anisotropic.NegativeNormalForm.CentralGaussianEnvelopes

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles

theorem gaussian_error_mono {g a D L : ℝ} (hga : g≤a) (hLD : L≤D) (N j : ℕ) :
    Real.exp (-a*(N:ℝ)^2+((j:ℝ)+1)*Real.log N+L*((j:ℝ)+1))≤
    Real.exp (-g*(N:ℝ)^2+((j:ℝ)+1)*Real.log N+D*((j:ℝ)+1)) := by
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right hga (sq_nonneg (N:ℝ))
  have h2 := mul_le_mul_of_nonneg_right hLD (show 0≤(j:ℝ)+1 by positivity)
  linarith

/-- The three literal analytic errors collapse to one Gaussian bound with the
sharp coefficient one on (j+1) log N. All constants precede m,j,d,s. -/
theorem central_analytic_errors_gaussian_bound
    (sigma cR KR MR Ma ca La rc Mc cc Lc K a : ℝ)
    (hsigma : 0<sigma) (hcR : 0<cR) (hKR : 0<KR) (hMR : 1≤MR)
    (hMa : 1≤Ma) (hca : 0<ca) (hLa : 0<La) (hrc : 0<rc)
    (hMc : 1≤Mc) (hcc : 0<cc) (hLc : 0<Lc) (hK : 0≤K) (ha : 0<a) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m : ℕ,0<m → ∀j : ℕ, ∀d s : ℝ,s≤sigma →
      2*(annularErrorEnvelope Ma ca La a m j+cycleErrorEnvelope rc Mc cc Lc K a m j+
          centeredRemainderEnvelope KR MR cR m j d s)≤
        Real.exp (-g*(2*m+1:ℕ)^2+((j:ℝ)+1)*Real.log (2*m+1:ℕ)+D*((j:ℝ)+1)) := by
  obtain ⟨ga,Da,hga,hDa,hann⟩ := annularErrorEnvelope_gaussian_bound Ma ca La a hMa hca hLa ha
  obtain ⟨gr,Dr,hgr,hDr,hrem⟩ := centeredRemainderEnvelope_gaussian_bound KR MR cR sigma hKR hMR hcR hsigma
  obtain ⟨Dc,hDc,hcy⟩ := cycleErrorEnvelope_global_bound rc Mc cc Lc K a
    hrc (lt_of_lt_of_le zero_lt_one hMc) hcc hLc hK ha
  let gc := Real.log 2/4
  have hgc : 0<gc := by dsimp [gc]; positivity
  let g := min ga (min gr gc)
  let D := Da+Dr+Dc
  have hg : 0<g := lt_min hga (lt_min hgr hgc)
  have hgg_a : g≤ga := min_le_left _ _
  have hgg_r : g≤gr := (min_le_right _ _).trans (min_le_left _ _)
  have hgg_c : g≤gc := (min_le_right _ _).trans (min_le_right _ _)
  have hDaD : Da≤D := by dsimp [D]; linarith
  have hDrD : Dr≤D := by dsimp [D]; linarith
  have hDcD : Dc≤D := by dsimp [D]; linarith
  have hl6 : 0<Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨g,D+Real.log 6,hg,by dsimp [D]; positivity,?_⟩
  intro m hm j d s hs
  have hA := (hann m j).trans (gaussian_error_mono hgg_a hDaD (2*m+1) j)
  have hR := (hrem m j d s hs).trans (gaussian_error_mono hgg_r hDrD (2*m+1) j)
  have hC : cycleErrorEnvelope rc Mc cc Lc K a m j≤
      Real.exp (-gc*(2*m+1:ℕ)^2+((j:ℝ)+1)*Real.log (2*m+1:ℕ)+Dc*((j:ℝ)+1)) := by
    simpa only [gc,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hcy m hm j
  have hC' := hC.trans (gaussian_error_mono hgg_c hDcD (2*m+1) j)
  let e := -g*(2*m+1:ℕ)^2+((j:ℝ)+1)*Real.log (2*m+1:ℕ)+D*((j:ℝ)+1)
  have hsum : 2*(annularErrorEnvelope Ma ca La a m j+cycleErrorEnvelope rc Mc cc Lc K a m j+
      centeredRemainderEnvelope KR MR cR m j d s)≤6*Real.exp e := by
    dsimp [e]
    linarith
  apply hsum.trans
  calc
    6*Real.exp e=Real.exp (Real.log 6+e) := by rw [Real.exp_add (Real.log 6) e,Real.exp_log (by norm_num : (0:ℝ)<6)]
    _≤_ := Real.exp_le_exp.mpr (by
      have hh := mul_nonneg (Nat.cast_nonneg j) hl6.le
      dsimp [e]
      nlinarith)

end
end IsingBulk.Anisotropic.NegativeNormalForm

import IsingBulk.Anisotropic.NegativeCycles.ComplexResidueBound
import IsingBulk.Anisotropic.NegativeCycles.FreeHomotopy
import IsingBulk.Anisotropic.NegativeCycles.ActualHomotopyPole

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped Topology

/-- The actual residue coefficient on the entire complex transport annulus.
The Gaussian particle factor and the all-order Taylor cost are derived uniformly. -/
theorem actualHomotopy_residue_uniform_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃δ M c : ℝ,0<δ ∧ 1≤M ∧ 0<c ∧ ∀m j : ℕ, ∀d : ℝ, |d|<δ →
      ∀P : UniformProjectedWitness B phi hphi (2*m+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀v : Fin (2*m+1)→ℝ, ‖fun i => (v i:ℂ)‖≤δ → (∑i,v i)=0 →
      ∀σ : ℝ,0<σ → σ≤∑i,v i^2 → ∀s : ℝ,s∈Icc (-1/2:ℝ) (3/2) →
      let z := correctedHomotopy P J s (fun i => (v i:ℂ))
      ‖poleResidue B rootB phi hphi (d:ℂ) P.T z/(P.T z)^(j+1)‖≤
        (2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
          ((8*(2*m+1:ℕ):ℝ)/σ)^(j+1) := by
  obtain ⟨a,M,c,ha,hM,hc,hres⟩ := poleResidue_complex_uniform_bound B rootB phi hphi hB hroot hBn
  obtain ⟨b,hb,hbR,hsector⟩ := actualHomotopy_pole_uniform_sector B phi hphi hB hBn r C R hr hR hRr
  have hcont : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
  have he : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<a/2 :=
    hcont.norm.eventually_lt continuousAt_const (by simpa using half_pos ha)
  obtain ⟨e,he,hes⟩ := Metric.mem_nhds_iff.mp he
  let δ := min b (min (a/8) (min e (R/4)))
  have hδ : 0<δ := lt_min hb (lt_min (by positivity) (lt_min he (by positivity)))
  have hδb : δ≤b := min_le_left _ _
  have hδa : δ≤a/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδe : δ≤e := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδR : δ≤R/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,M,c,hδ,hM,hc,?_⟩
  intro m j d hd P J v hv hm σ hσ hσQ s hs
  dsimp only
  let y : Config (2*m+1) := fun i => (v i:ℂ)
  let z := correctedHomotopy P J s y
  have hmy : ZeroMean y := by
    change (∑i,(v i:ℂ))=0
    exact_mod_cast hm
  have hyR : ‖y‖≤R/2 := by dsimp only [y]; linarith
  have hz := correctedHomotopy_norm_le P J hr hR hRr s hs y hyR
  have hzsmall : ‖z‖<2*r := by dsimp only [z,y] at *; linarith
  have htau := hes (show (d:ℂ)∈ball (0:ℂ) e by simpa using hd.trans_le hδe)
  change ‖1-Complex.cos (d:ℂ)‖<a/2 at htau
  have hl := P.t_lip z 0 hzsmall (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hr)
  rw [P.t_zero,sub_zero] at hl
  have htA : ‖P.T z‖<a := by
    have hh := norm_add_le (P.T z-(1-Complex.cos (d:ℂ))) (1-Complex.cos (d:ℂ))
    rw [sub_add_cancel] at hh
    dsimp only [y] at hz
    linarith
  have hdA : ‖(d:ℂ)‖<a := by simpa using (show |d|<a by linarith)
  have hRbound := hres m (d:ℂ) P.T z hdA htA (fun i => by
    have hh := norm_le_pi_norm z i
    dsimp only [y] at hz
    linarith)
  have hsec := hsector (2*m+1) (by omega) d (by simpa using hd.trans_le hδb) P J v
    (hv.trans hδb) hm s hs
  have hn : (0:ℝ)<(2*m+1:ℕ) := by positivity
  have hgap : σ/(8*(2*m+1:ℕ))≤‖P.T z‖ := by
    have hq := div_le_div_of_nonneg_right hσQ (show (0:ℝ)≤8*(2*m+1:ℕ) by positivity)
    have hrnorm := Complex.re_le_norm (P.T z)
    have hcos := Real.cos_le_one d
    dsimp only [z,y] at hrnorm ⊢
    linarith
  exact poleResidue_quotient_norm_le (by omega) hc hσ (by positivity) hRbound hgap j

end IsingBulk.Anisotropic.NegativeCycles

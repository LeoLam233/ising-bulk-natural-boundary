import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectedEuclidean
import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set
open scoped BigOperators

theorem absoluteEnergy_add_le {n : ℕ} (v e : Config n) :
    absoluteEnergy (v+e)≤2*absoluteEnergy v+2*absoluteEnergy e := by
  unfold absoluteEnergy
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := norm_add_le (v i) (e i)
  change ‖v i+e i‖^2≤_
  nlinarith [sq_nonneg (‖v i‖-‖e i‖),norm_nonneg (v i+e i),norm_nonneg (v i),norm_nonneg (e i)]

/-- The entire enlarged real homotopy has a dimension-free positive quadratic sector. -/
theorem straightConfig_sector {n : ℕ} (v : Fin n→ℝ) (e : Config n) (s : ℝ)
    (hs : s∈Icc (-1/2:ℝ) (3/2))
    (he : absoluteEnergy e≤(∑i,v i^2)/64) :
    (7/16:ℝ)*(∑i,v i^2)≤(quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)).re ∧
      absoluteEnergy (fun i => (v i:ℂ)+(s:ℂ)*e i)≤3*(∑i,v i^2) := by
  let E : Config n := fun i => (s:ℂ)*e i
  have hq : 0≤∑i,v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hE : absoluteEnergy E≤(∑i,v i^2)/16 := by
    dsimp only [E]
    rw [absoluteEnergy_scale]
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    have hsq : s^2≤(9/4:ℝ) := by nlinarith [hs.1,hs.2]
    have hprod := mul_le_mul_of_nonneg_left he (sq_nonneg s)
    have hprod' := mul_le_mul_of_nonneg_right hsq (show 0≤(∑i,v i^2)/64 by positivity)
    nlinarith
  have hroot : Real.sqrt (absoluteEnergy E)≤(1/4)*Real.sqrt (∑i,v i^2) := by
    have h1 := Real.sq_sqrt (absoluteEnergy_nonneg E)
    have h2 := Real.sq_sqrt hq
    have h3 := Real.sqrt_nonneg (absoluteEnergy E)
    have h4 := Real.sqrt_nonneg (∑i,v i^2)
    nlinarith
  constructor
  · convert quadratic_real_perturbation_lower v E (1/4) (by norm_num) hroot using 1; norm_num
  · have h := absoluteEnergy_add_le (fun i => (v i:ℂ)) E
    rw [absoluteEnergy_real] at h
    change absoluteEnergy (fun i => (v i:ℂ)+E i)≤_ at h ⊢
    linarith

/-- Actual pole comparisons exclude zero along the whole homotopy, not just at its ends. -/
theorem straightConfig_pole_re_lower {n : ℕ} (hn : n≠0)
    (v : Fin n→ℝ) (e : Config n) (s d : ℝ) (t : ℂ)
    (hs : s∈Icc (-1/2:ℝ) (3/2))
    (he : absoluteEnergy e≤(∑i,v i^2)/64)
    (ht : ‖t-(1-Complex.cos (d:ℂ))-
      quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)/(2*n)‖≤
      absoluteEnergy (fun i => (v i:ℂ)+(s:ℂ)*e i)/(64*n)) :
    1-Real.cos d+(∑i,v i^2)/(8*n)≤t.re := by
  obtain ⟨hQ,hq⟩ := straightConfig_sector v e s hs he
  have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hreal := (abs_le.mp (Complex.abs_re_le_norm
    (t-(1-Complex.cos (d:ℂ))-quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)/(2*n)))).1
  have hdiv : (quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)/(2*(n:ℂ))).re=
      (quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)).re/(2*(n:ℝ)) := by
    convert Complex.div_ofReal_re (quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)) (2*(n:ℝ)) using 1; push_cast; rfl
  have hre : (t-(1-Complex.cos (d:ℂ))-
      quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)/(2*n)).re=
      t.re-(1-Real.cos d)-(quadratic (fun i => (v i:ℂ)+(s:ℂ)*e i)).re/(2*n) := by
    rw [Complex.sub_re,Complex.sub_re,Complex.sub_re,Complex.one_re,
      ←Complex.ofReal_cos,Complex.ofReal_re,hdiv]
  rw [hre] at hreal
  have hT : absoluteEnergy (fun i => (v i:ℂ)+(s:ℂ)*e i)/(64*n)≤
      (3*(∑i,v i^2))/(64*n) := div_le_div_of_nonneg_right hq (by positivity)
  have hQr := div_le_div_of_nonneg_right hQ (show 0≤2*(n:ℝ) by positivity)
  have h : 1-Real.cos d+(7/16:ℝ)*(∑i,v i^2)/(2*n)-3*(∑i,v i^2)/(64*n)≤t.re := by linarith
  apply le_trans _ h
  have hq0 : 0≤∑i,v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  field_simp
  nlinarith

end IsingBulk.Anisotropic.NegativeCycles

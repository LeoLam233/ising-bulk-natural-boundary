import IsingBulk.Tail.MixedSeparatedDomain

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem mixedSeparated_tau_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => mixedSourceTau s (deformedPoint f r τ lam θ i)) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  have hsi := ((ParameterSmoothOn.parameter Ω).pow 2).inv (fun _ h => pow_ne_zero _ h.1)
  have hn := (ParameterSmoothOn.const Ω (-1)).mul ((ParameterSmoothOn.const Ω 1).sub hsi)
  have hsin := (mixedSeparated_phase_smooth J j q f hr τ lam hp hm i).complex_comp Complex.sin (by intro p _; fun_prop)
  simpa only [neg_one_mul,mixedSourceTau] using hn.div hsin (fun _ h => mixedSourcePhase_sin_ne (h.2.1 i))

theorem mixedSeparated_A_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) (hi : i∈J) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => mixedSourceA s (deformedPoint f r τ lam θ i)) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  have hsi := ((ParameterSmoothOn.parameter Ω).pow 2).inv (fun _ h => pow_ne_zero _ h.1)
  have hy := mixedSeparated_y_smooth J j q f r τ lam hp hm i
  have hd := ((ParameterSmoothOn.const Ω (-Complex.I)).mul
    (hy.sub (hy.inv (fun p _ => deformedPoint_nonzero f hr.ne' τ lam p.2 i)))).div
    (ParameterSmoothOn.const Ω 2) (by intro p _; norm_num)
  exact ((ParameterSmoothOn.const Ω 1).sub hsi).div hd (fun p h =>
    div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (h.2.2.1 i hi)) (by norm_num))

theorem mixedSeparated_velocity_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => mixedContourVelocity J j q f r τ lam s θ i) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  let A := fun s θ => ∑ k∈J,mixedSourceA s (deformedPoint f r τ lam θ k)
  let D := fun s θ => ∑ k∈Finset.univ.filter (fun k => k∉J),mixedSourceTau s (deformedPoint f r τ lam θ k)
  let b := fun (k : Fin N) (s : ℂ) (θ : Fin N → ℝ) => mixedSourceSlope s (deformedPoint f r τ lam θ k)
  let X := fun s θ => (D s θ+b q s θ*A s θ)/(b j s θ-b q s θ)
  have hA : ParameterSmoothOn Ω A := ParameterSmoothOn.sum J _ (fun k hk => mixedSeparated_A_smooth J j q f hr τ lam hp hm k hk)
  have hD : ParameterSmoothOn Ω D := ParameterSmoothOn.sum _ _ (fun k _ => mixedSeparated_tau_smooth J j q f hr τ lam hp hm k)
  have hb (k : Fin N) : ParameterSmoothOn Ω (b k) := mixedSeparated_slope_smooth J j q f hr τ lam hp hm k
  have hX : ParameterSmoothOn Ω X := (hD.add ((hb q).mul hA)).div ((hb j).sub (hb q)) (fun _ h => h.2.2.2.1)
  have hfirst : ParameterSmoothOn Ω (fun s θ => if i∈J then mixedSourceA s (deformedPoint f r τ lam θ i) else 0) := by
    by_cases hi : i∈J
    · simpa only [hi,ite_true] using mixedSeparated_A_smooth J j q f hr τ lam hp hm i hi
    · simpa only [hi,ite_false] using ParameterSmoothOn.const Ω 0
  have hsecond : ParameterSmoothOn Ω (fun s θ => if i=j then X s θ else 0) := by
    by_cases hij : i=j
    · simpa only [hij,ite_true] using hX
    · simpa only [hij,ite_false] using ParameterSmoothOn.const Ω 0
  have hthird : ParameterSmoothOn Ω (fun s θ => if i=q then A s θ+X s θ else 0) := by
    by_cases hiq : i=q
    · simpa only [hiq,ite_true] using hA.add hX
    · simpa only [hiq,ite_false] using ParameterSmoothOn.const Ω 0
  exact (hfirst.add hsecond).sub hthird

end
end IsingBulk.Tail

import IsingBulk.Tail.RealPolynomialJets
import IsingBulk.Tail.AllBranchExteriorWeights

/-! Rational pair weights for any fixed allowed pair set. This includes a
set that excludes a named current coordinate. The estimates retain the
selected separation independently of the diameter of that set. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

def compactPairWeightDenom {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ) (θ : Fin N → ℝ) : ℝ :=
  ∑ p ∈ P, (θ p.1-θ p.2)^(2*M)

def compactPairWeight {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ)
    (i j : Fin N) (θ : Fin N → ℝ) : ℝ :=
  (θ i-θ j)^(2*M)/compactPairWeightDenom P M θ

theorem compactPairWeightDenom_nonneg {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (θ : Fin N → ℝ) : 0 ≤ compactPairWeightDenom P M θ :=
  Finset.sum_nonneg (fun p _ => by rw [pow_mul]; positivity)

theorem compactPairWeightDenom_lower {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (θ : Fin N → ℝ) (d : ℝ) (hatt : ∃ p ∈ P, |θ p.1-θ p.2|=d) :
    d^(2*M) ≤ compactPairWeightDenom P M θ := by
  obtain ⟨p,hp,he⟩ := hatt
  have hh := Finset.single_le_sum (s := P) (f := fun q => (θ q.1-θ q.2)^(2*M))
    (fun q _ => by rw [pow_mul]; positivity) hp
  rw [← he,pow_mul,sq_abs]
  simpa only [compactPairWeightDenom,pow_mul] using hh

theorem compactPairWeight_sum {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (θ : Fin N → ℝ) (h : compactPairWeightDenom P M θ ≠ 0) :
    (∑ p ∈ P, compactPairWeight P M p.1 p.2 θ)=1 := by
  unfold compactPairWeight
  rw [← Finset.sum_div]
  exact div_self h

theorem compactPairWeightDenom_scaled {N : ℕ} (P : Finset (Fin N × Fin N))
    (M J : ℕ) (hM : 0 < M) (x : ℂ × (Fin N → ℝ)) (d : ℝ) (hd : 0 < d)
    (hp : ∀ p ∈ P, |x.2 p.1-x.2 p.2| ≤ d) :
    RealScaledJetBound (fun y : ℂ × (Fin N → ℝ) => (compactPairWeightDenom P M y.2:ℂ))
      x J d ((N:ℝ)^2*(2^(2*M)*(2*M:ℕ)^J)) (2*M:ℕ) := by
  have hf (p : Fin N × Fin N) (h : p ∈ P) :=
    (jointAngularDifference_scaled p.1 p.2 x J d hd (hp p h)).pow hd (2*M) (by omega)
  have hsum := RealScaledJetBound.finset_sum P hf
    (show 0 ≤ (2:ℝ)^(2*M)*(2*M:ℕ)^J by positivity)
  have hsum' : RealScaledJetBound
      (fun y : ℂ × (Fin N → ℝ) => (compactPairWeightDenom P M y.2:ℂ)) x J d
      ((P.card:ℝ)*(2^(2*M)*(2*M:ℕ)^J)) (2*M:ℕ) := by
    simpa only [compactPairWeightDenom,Complex.ofReal_sum,Complex.ofReal_pow,one_mul] using hsum
  apply hsum'.mono hd le_rfl
  have hcard : (P.card:ℝ) ≤ (N:ℝ)^2 := by
    have hh := Finset.card_le_univ P
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,Nat.cast_mul] using
      (Nat.cast_le.mpr hh : (P.card:ℝ) ≤ Fintype.card (Fin N × Fin N))
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

theorem compactPairWeightDenom_inverse_jets {N : ℕ} (P : Finset (Fin N × Fin N))
    (M J : ℕ) (hM : 0 < M) (x : ℂ × (Fin N → ℝ)) (d : ℝ) (hd : 0 < d)
    (hp : ∀ p ∈ P, |x.2 p.1-x.2 p.2| ≤ d) (hatt : ∃ p ∈ P, |x.2 p.1-x.2 p.2|=d) :
    RealScaledJetBound (fun y : ℂ × (Fin N → ℝ) => ((compactPairWeightDenom P M y.2:ℂ))⁻¹)
      x J d ((J.factorial:ℝ)^2*(max 1 ((N:ℝ)^2*(2^(2*M)*(2*M:ℕ)^J)))^J) (-(2*M:ℕ)) := by
  have hh := (compactPairWeightDenom_scaled P M J hM x d hd hp).inv hd zero_lt_one
    (show (1:ℝ)*d^((2*M:ℕ):ℤ) ≤ ‖(compactPairWeightDenom P M x.2:ℂ)‖ by
      rw [one_mul,zpow_natCast,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (compactPairWeightDenom_nonneg P M x.2)]
      exact compactPairWeightDenom_lower P M x.2 d hatt)
  simpa only [inv_one,max_self,one_pow,mul_one] using hh

theorem RealScaledJetBound.smaller_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} {J : ℕ} {d ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J d C a) (hd : 0 < d) (hρ : 0 < ρ) (hρd : ρ ≤ d) :
    RealScaledJetBound f x J ρ (C*d^a) 0 := by
  refine ⟨h.smooth,mul_nonneg h.nonneg (zpow_nonneg hd.le _),?_⟩
  intro k hk
  calc
    _ ≤ C*d^(a-(k:ℤ)) := h.bound k hk
    _ = (C*d^a)*(d⁻¹)^k := by rw [mul_assoc,scaled_jet_power_identity d hd]
    _ ≤ (C*d^a)*(ρ⁻¹)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hd.le) (inv_anti₀ hρ hρd) k)
      (mul_nonneg h.nonneg (zpow_nonneg hd.le _))
    _ = _ := by rw [zero_sub,zpow_neg,zpow_natCast,inv_pow]

/-- The weight keeps its selected zero of order 2M while its denominator
is measured at the diameter of the allowed pair set. -/
theorem compactPairWeight_selected_jets {N : ℕ} (P : Finset (Fin N × Fin N))
    (M J : ℕ) (hM : 0 < M) (x : ℂ × (Fin N → ℝ)) (d ρ : ℝ)
    (hd : 0 < d) (hρ : 0 < ρ) (hρd : ρ ≤ d)
    (hp : ∀ p ∈ P, |x.2 p.1-x.2 p.2| ≤ d) (hatt : ∃ p ∈ P, |x.2 p.1-x.2 p.2|=d)
    (i j : Fin N) (hsel : |x.2 i-x.2 j| ≤ ρ) :
    RealScaledJetBound
      (fun y : ℂ × (Fin N → ℝ) => (compactPairWeight P M i j y.2:ℂ)) x J ρ
      (2^J*(2^(2*M)*(2*M:ℕ)^J)*
        (((J.factorial:ℝ)^2*(max 1 ((N:ℝ)^2*(2^(2*M)*(2*M:ℕ)^J)))^J)*d^(-(2*M:ℕ):ℤ)))
      (2*M:ℕ) := by
  have hn := (jointAngularDifference_scaled i j x J ρ hρ hsel).pow hρ (2*M) (by omega)
  have hi := (compactPairWeightDenom_inverse_jets P M J hM x d hd hp hatt).smaller_scale hd hρ hρd
  have hh := hn.mul hi hρ
  simpa only [compactPairWeight,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,
    one_mul,add_zero] using hh

end
end IsingBulk.Tail

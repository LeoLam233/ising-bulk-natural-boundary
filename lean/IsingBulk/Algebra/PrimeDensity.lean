import IsingBulk.Algebra.NickelOrder

/-! Density of the actual family, with distinct neighboring integer indices. -/
namespace IsingBulk.PrimeFamily
noncomputable section

theorem neighboring_prime_angles {t ε : ℝ} (ht : 0 < t) (htπ : t < Real.pi / 2)
    (hε : 0 < ε) :
    ∃ p : ℕ, ∃ a b : ℤ, p.Prime ∧ 11 ≤ p ∧ a ≠ b ∧ Admissible p a ∧ Admissible p b ∧
      |angle p a - t| < ε ∧ |angle p b - t| < ε := by
  let δ := min t (min (Real.pi / 2 - t) ε)
  have hδ : 0 < δ := lt_min ht (lt_min (sub_pos.mpr htπ) hε)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.pi / δ)
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (max M 11)
  have hp11 : 11 ≤ p := (le_max_right M 11).trans hpM
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hMp : (M : ℝ) ≤ p := by exact_mod_cast (le_max_left M 11).trans hpM
  let h : ℝ := 2 * Real.pi / p
  have hh : 0 < h := div_pos (by positivity) hpR
  have hhδ : h < δ := by
    apply (div_lt_iff₀ hpR).mpr
    have := (div_lt_iff₀ hδ).mp (hM.trans_le hMp)
    nlinarith
  have hht : h < t := hhδ.trans_le (min_le_left _ _)
  have hhπ : h < Real.pi / 2 - t := hhδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhε : h < ε := hhδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let a : ℤ := ⌊t / h⌋
  let b : ℤ := a + 1
  have ha : (a : ℝ) ≤ t / h := Int.floor_le _
  have hb : t / h < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have ha' : h * (a : ℝ) ≤ t := by nlinarith [(le_div_iff₀ hh).mp ha]
  have hb' : t < h * ((a : ℝ) + 1) := by nlinarith [(div_lt_iff₀ hh).mp hb]
  have ea : angle p a = h * (a : ℝ) := by unfold angle h; ring
  have eb : angle p b = h * ((a : ℝ) + 1) := by unfold angle b h; push_cast; ring
  refine ⟨p, a, b, hp, hp11, by dsimp [b]; omega, ?_, ?_, ?_, ?_⟩
  · unfold Admissible
    rw [ea]
    constructor <;> linarith
  · unfold Admissible
    rw [eb]
    constructor <;> linarith
  · rw [ea, abs_lt]
    constructor <;> linarith
  · rw [eb, abs_lt]
    constructor <;> linarith

/-- The set uses the source's prime bound and distinct admissible integers. -/
def selectedFamily : Set ℂ :=
  {z | ∃ p : ℕ, ∃ a b : ℤ, p.Prime ∧ 11 ≤ p ∧ a ≠ b ∧ Admissible p a ∧ Admissible p b ∧
    z = selectedPoint p a b}

/-- Every point on the open upper-right arc is in the closure of the selected family. -/
theorem selectedFamily_dense_arc {t : ℝ} (ht : 0 < t) (htπ : t < Real.pi / 2) :
    Complex.exp ((t : ℂ) * Complex.I) ∈ closure selectedFamily := by
  let f : ℝ × ℝ → ℂ := fun x =>
    Complex.exp ((Real.arccos ((Real.cos x.1 + Real.cos x.2) / 2) : ℂ) * Complex.I)
  have hg : Continuous (fun x : ℝ × ℝ => (Real.cos x.1 + Real.cos x.2) / 2) :=
    ((Real.continuous_cos.comp continuous_fst).add
      (Real.continuous_cos.comp continuous_snd)).div_const 2
  have hf : Continuous f := Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (Real.continuous_arccos.comp hg)).mul_const Complex.I)
  have hft : f (t,t) = Complex.exp ((t : ℂ) * Complex.I) := by
    dsimp [f]
    rw [show (Real.cos t + Real.cos t) / 2 = Real.cos t by ring,
      Real.arccos_cos ht.le (by linarith [Real.pi_pos])]
  rw [← hft, Metric.mem_closure_iff]
  intro ε hε
  have hfAt : ContinuousAt f (t,t) := hf.continuousAt
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hfAt ε hε
  obtain ⟨p, a, b, hp, hp11, hab, ha, hb, hea, heb⟩ := neighboring_prime_angles ht htπ hδ
  refine ⟨selectedPoint p a b, ⟨p, a, b, hp, hp11, hab, ha, hb, rfl⟩, ?_⟩
  have hd : dist (angle p a, angle p b) (t,t) < δ := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro hea heb
  rw [dist_comm]
  simpa only [f, selectedPoint, cosineAverage] using hcont hd

end
end IsingBulk.PrimeFamily

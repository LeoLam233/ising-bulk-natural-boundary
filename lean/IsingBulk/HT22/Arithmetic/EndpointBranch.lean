import IsingBulk.HT22.Arithmetic.PrimeRoot

/-! The actual F001 branch `exp(-i arccos(|2 cos α|-1))`, with the absolute
value required for the second upper quadrant. -/
namespace IsingBulk.HT22.Arithmetic
noncomputable section
open Polynomial IntermediateField IsingBulk.PrimeFamily

def endpointBranch (p : ℕ) (a : ℤ) : ℂ :=
  Complex.exp (-(Real.arccos (|2*Real.cos (angle p a)|-1):ℂ)*Complex.I)

theorem endpointBranch_relation (p : ℕ) (a : ℤ) :
    endpointBranch p a+(endpointBranch p a)⁻¹ =
      ((2*|2*Real.cos (angle p a)|-2:ℝ):ℂ) := by
  have hab : |2*Real.cos (angle p a)|≤2 := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [Real.abs_cos_le_one (angle p a)]
  have ht : Real.cos (Real.arccos (|2*Real.cos (angle p a)|-1)) =
      |2*Real.cos (angle p a)|-1 :=
    Real.cos_arccos (by linarith [abs_nonneg (2*Real.cos (angle p a))]) (by linarith)
  have hz := exp_angle_add_inv (-Real.arccos (|2*Real.cos (angle p a)|-1))
  simp only [Complex.ofReal_neg,Real.cos_neg,ht] at hz
  change endpointBranch p a+(endpointBranch p a)⁻¹=_ at hz
  rw [hz]
  push_cast
  ring

theorem endpointBranch_signed_relation (p : ℕ) (a : ℤ) :
    ∃ ε : ℚ, (ε=1 ∨ ε= -1) ∧
      endpointBranch p a+(endpointBranch p a)⁻¹ =
        (2*ε) • (angleRoot p a+(angleRoot p a)⁻¹)-2 := by
  have hroot := exp_angle_add_inv (angle p a)
  change angleRoot p a+(angleRoot p a)⁻¹=_ at hroot
  by_cases hs : 0≤2*Real.cos (angle p a)
  · refine ⟨1,Or.inl rfl,?_⟩
    rw [endpointBranch_relation,abs_of_nonneg hs,hroot]
    norm_num only [Algebra.smul_def,map_mul,map_ofNat,map_one]
    push_cast
    ring
  · refine ⟨-1,Or.inr rfl,?_⟩
    rw [endpointBranch_relation,abs_of_neg (lt_of_not_ge hs),hroot]
    norm_num only [Algebra.smul_def,map_mul,map_ofNat,map_neg,map_one]
    push_cast
    ring

theorem endpointBranch_algebraic_nonresonant {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    IsAlgebraic ℚ (endpointBranch p a) ∧ ¬ IsOfFinOrder (endpointBranch p a) := by
  obtain ⟨ε,hε,hrel⟩ := endpointBranch_signed_relation p a
  have hr := primeIndex_primitive hp ha
  have hra : IsAlgebraic ℚ (angleRoot p a) := (hr.isIntegral hp.pos).tower_top.isAlgebraic
  have htwo : IsAlgebraic ℚ (2:ℂ) := by simpa using (isAlgebraic_algebraMap (R:=ℚ) (A:=ℂ) 2)
  have hw := (((hra.add hra.inv).smul (2*ε)).sub htwo)
  have hz0 : endpointBranch p a≠0 := Complex.exp_ne_zero _
  have hza := algebraic_of_add_inv hz0 hw hrel
  refine ⟨hza,?_⟩
  let r : AlgebraicComplex := ⟨angleRoot p a,mem_algebraicClosure_iff.mpr hra⟩
  let z : AlgebraicComplex := ⟨endpointBranch p a,mem_algebraicClosure_iff.mpr hza⟩
  have hr' : IsPrimitiveRoot r p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hr
  have hz0' : z≠0 := fun h => hz0 (congrArg (fun z : AlgebraicComplex => (z:ℂ)) h)
  have hrel' : z+z⁻¹=(2*ε) • (r+r⁻¹)-2 := Subtype.ext hrel
  intro hfin
  apply signed_branch_trace_obstruction hp hp5 hr' hz0' hε hrel'
  obtain ⟨N,hN,hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨N,hN,Subtype.ext hpow⟩

/-- All positive powers avoid both signs, as needed for both signed kernels. -/
theorem endpointBranch_pow_ne_signs {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (N : ℕ) (hN : 0<N) :
    endpointBranch p a^N≠1 ∧ endpointBranch p a^N≠ -1 := by
  have hnr := (endpointBranch_algebraic_nonresonant hp hp5 ha).2
  constructor
  · exact fun h => hnr (isOfFinOrder_iff_pow_eq_one.mpr ⟨N,hN,h⟩)
  · intro h
    apply hnr
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2*N,by omega,?_⟩
    rw [Nat.mul_comm 2 N,pow_mul,h]
    norm_num

end
end IsingBulk.HT22.Arithmetic

import IsingBulk.HT22.Final.NaturalBoundary

/-! An actual finite truncation of the physical angular odd coefficients is
provably not equal to the actual infinite exterior source. The control uses
the new first-coefficient/noncancellation chain and genuine lower-order limits. -/
namespace IsingBulk.HT22.Controls
noncomputable section
open Physical Arithmetic IsingBulk.PrimeFamily IsingBulk.Branch
open Set Filter
open scoped Topology BigOperators

def finiteOddPrefix (m : ℕ) (t : ℂ) : ℂ :=
  ∑ n ∈ Finset.range m, coefficient (2*n+1) t

theorem angle_one_positive_sign {p : ℕ} (hp5 : 5≤p) :
    negativeSide (angle p 1)=false := by
  have hp : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hp4 : (4:ℝ)<p := by exact_mod_cast (show 4<p by omega)
  have hangle : angle p 1<Real.pi/2 := by
    unfold angle
    simp only [Int.cast_one,mul_one]
    apply (div_lt_iff₀ hp).mpr
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hp4)]
  simp [negativeSide,not_lt.mpr hangle.le]

theorem finiteOddPrefix_iteratedDeriv (m j : ℕ) {t : ℂ} (ht : 1<‖t‖) :
    iteratedDeriv j (finiteOddPrefix m) t=
      ∑ n∈Finset.range m,iteratedDeriv j (coefficient (2*n+1)) t := by
  exact iteratedDeriv_fun_sum (fun n _ => (coefficient_analyticAt (2*n+1) ht).contDiffAt)

theorem finiteOddPrefix_epsilon_zero {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {m : ℕ} (hmp : 2*m+1<p) (j : ℕ) :
    Tendsto (fun ε : ℝ => ε •
      (∑ n∈Finset.range m, iteratedDeriv j (coefficient (2*n+1))
        (radialParameter (primeBranchData hp hp5
          (show PrimeIndex p 1 from ⟨by norm_num,by omega⟩)).alpha ε)))
      (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  have ha : PrimeIndex p 1 := ⟨by norm_num,by omega⟩
  have hsign := angle_one_positive_sign hp5
  have hl (n : ℕ) (hn : n∈Finset.range m) :=
    Finite.prime_lower_coefficient_limit hp hp5 ha (show Odd (2*n+1) from ⟨n,rfl⟩)
      (show 2*n+1<p by have := Finset.mem_range.mp hn;omega) j
  have hsum := tendsto_finsetSum (Finset.range m) hl
  have hcoeff : signedCoefficient false=coefficient := rfl
  simpa only [hsign,hcoeff,Finset.sum_const_zero,Finset.smul_sum] using hsum

/-- No fixed finite number of actual odd coefficients can replace the infinite
physical exterior source, even by equality only on the open exterior domain. -/
theorem finiteOddPrefix_not_full (m : ℕ) :
    ¬EqOn oddSeries (finiteOddPrefix m) {t : ℂ | 1<‖t‖} := by
  obtain ⟨p,hbound,hp⟩ := Nat.exists_infinite_primes (2*m+6)
  have hp5 : 5≤p := by omega
  have hmp : 2*m+1<p := by omega
  have ha : PrimeIndex p 1 := ⟨by norm_num,by omega⟩
  let d := primeBranchData hp hp5 ha
  let j := IsingBulk.HT.First.derivativeOrder p
  have hsign := angle_one_positive_sign hp5
  obtain ⟨hne,hfull⟩ := Final.actual_prime_full_limit hp hp5 ha
  have hzero := finiteOddPrefix_epsilon_zero hp hp5 hmp j
  intro heq
  have hderiv : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      iteratedDeriv j (signedOddSeries (negativeSide (angle p 1)))
        (radialParameter d.alpha ε)=
      ∑ n∈Finset.range m,iteratedDeriv j (coefficient (2*n+1))
        (radialParameter d.alpha ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have ht : 1<‖radialParameter d.alpha ε‖ := by
      rw [IsingBulk.First.radialParameter_norm (le_of_lt hε)]
      exact lt_add_of_pos_right 1 hε
    have hevent : oddSeries =ᶠ[𝓝 (radialParameter d.alpha ε)] finiteOddPrefix m := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ht] with t ht
      exact heq ht
    rw [hsign]
    change iteratedDeriv j oddSeries _ = _
    exact (hevent.iteratedDeriv_eq j).trans (finiteOddPrefix_iteratedDeriv m j ht)
  have hzero' : Tendsto (fun ε : ℝ => ε •
      iteratedDeriv j (signedOddSeries (negativeSide (angle p 1)))
        (radialParameter d.alpha ε)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    apply hzero.congr'
    filter_upwards [hderiv] with ε he
    rw [he]
  exact hne (tendsto_nhds_unique hfull hzero')

end
end IsingBulk.HT22.Controls

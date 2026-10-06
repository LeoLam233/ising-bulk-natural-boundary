/- INTENTIONALLY INVALID. Excluded from production imports and declaration counts. -/
example : (2 : Nat) ≤ 2 → (2 : Nat) < 2 := by
  intro h
  -- EXPECT_FAILURE_HERE: a weak endpoint cannot prove a strict endpoint.
  exact h

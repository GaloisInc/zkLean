-- no imports
theorem silly : True := by
  have h0 : True := trivial
  have h1 : True := h0
  have h2 : True := h1
  have h3 : True := h2
  -- copy expand until ~4000 lines
  -- (I can generate them)
  exact trivial

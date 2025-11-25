-- no imports
def megaTuple :=
  (1,
    (2,
      (3,
        (4,
          (5,
            (6,
              (7,
                (8,
                  (9,
                    (10,
                      -- continue until ~30k depth
                      (30000, 0)
))))))))))

theorem megaTuple_ok : True := trivial

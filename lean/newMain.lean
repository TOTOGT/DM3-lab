-- Main.lean — dm³ Toy Machine Demo
import AXLE  -- adjust the import path if your main file is named differently

#eval "=== dm³ Toy Machine Demo ==="

#eval "Normalized hexagonalEigenmode normalization check: " ++ toString (∑ i, (hexagonalEigenmode i) ^ 2 * weight i = 1)

def toy_start := simpleEmbedding 27   -- Collatz number that takes 111 steps in reality

#eval "Starting PhaseVector for n = 27: " ++ toString toy_start

def after_5_steps := applyG^[5] toy_start

#eval "After 5 dm³ steps: " ++ toString after_5_steps

#eval "Is saturated after 5 steps? " ++ toString (isCrystalSaturated after_5_steps)

#eval "=== End of Demo ==="

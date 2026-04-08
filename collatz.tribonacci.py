import math

def collatz_step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1

def collatz_orbit(n: int, max_steps: int = 2000):
    orbit = []
    while n != 1 and len(orbit) < max_steps:
        orbit.append(n)
        n = collatz_step(n)
    orbit.append(1)
    return orbit

def log_entropy_orbit(n: int):
    return [math.log(x) for x in collatz_orbit(n) if x > 0]

def tribonacci(k: int):
    a, b, c = 0, 0, 1
    seq = []
    for _ in range(k):
        seq.append(c)
        a, b, c = b, c, a + b + c
    return seq

if __name__ == "__main__":
    N = 5000
    peaks = [max(log_entropy_orbit(n)) for n in range(2, N)]
    peaks.sort()

    print("Sample peak log-entropies:", peaks[:20])
    print("Tribonacci:", tribonacci(20))

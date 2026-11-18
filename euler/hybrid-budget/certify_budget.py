#!/usr/bin/env python3
"""Exact rational certificates for a conditional Euler 1747 hybrid budget.

Uses integer powers and Fraction throughout. This is not a Lean proof.
"""
from fractions import Fraction as F

SCALE = 10**24
RHO = F(127, 128)
OLD_CUTOFF = 64**4


def upper_power(base, exponent):
    """Upper bound base**exponent by an exact rational with denominator SCALE."""
    base, exponent = F(base), F(exponent)
    target = base ** exponent.numerator
    degree = exponent.denominator
    numerator = target.numerator * SCALE**degree
    denominator = target.denominator
    low, high = 0, 1
    while high**degree * denominator < numerator:
        high *= 2
    while high - low > 1:
        middle = (low + high) // 2
        if middle**degree * denominator >= numerator:
            high = middle
        else:
            low = middle
    result = F(high, SCALE)
    assert result**degree >= target
    return result


def envelope(n, beta, constant=F(1)):
    """Bound for P=floor(2*n**((1-beta)/2)), assuming 2*n**a >= 128."""
    beta, constant = F(beta), F(constant)
    factor_two = upper_power(2, F(4, 5) - beta)
    leading = (F(46, 225) * constant * factor_two + F(44, 225) / RHO)
    lower = F(23, 30) * constant * factor_two + F(22, 15) / RHO**2
    terms = [
        F(21, 50),
        leading * upper_power(n, (beta - F(3, 5)) / 2),
        lower * upper_power(n, beta - F(4, 5)),
        F(88, 225) * upper_power(n, -F(3, 10)),
        F(44, 15) * upper_power(n, -F(4, 5)),
    ]
    return sum(terms), terms


def cutoff_condition(n, beta):
    exponent = (1 - F(beta)) / 2
    return F(n)**exponent.numerator >= F(64)**exponent.denominator


def ceil_decimal(value, places=8):
    """Display a rational upper bound, rounded upward without floats."""
    scale = 10**places
    scaled = (value.numerator * scale + value.denominator - 1) // value.denominator
    return f"{scaled // scale}.{scaled % scale:0{places}d}"


def extra_cases(n):
    """All positive n=2 mod 4 in (64**4, n], before the m-factor reduction."""
    return max(0, (n + 2)//4 - (OLD_CUTOFF + 2)//4)


def check_original_paper_arithmetic():
    total = (
        F(21, 50)
        + F(23, 30)*F(5, 4)*F(4, 9)*(F(4, 15)+F(1, 64))
        + F(44, 15)*F(4, 9)*(F(1, 15)+F(19, 30*64)+F(1, 64**3))
    )
    assert total == F(21235493, 33177600)
    assert F(2, 3) - total == F(882907, 33177600)
    assert F(64)**1 * F(4, 9)**5 >= 1
    assert F(2)**3 < F(5, 4)**10
    return total


def main():
    total = check_original_paper_arithmetic()
    print("Paper rational total:", total)
    print("Paper strict margin:", F(2, 3)-total)
    bound, terms = envelope(OLD_CUTOFF, F(1, 2))
    assert cutoff_condition(OLD_CUTOFF, F(1, 2))
    assert bound < F(2, 3)
    print("C=1 beta=1/2 at 64^4: upper bound", ceil_decimal(bound))
    beta = F(11, 20)
    n = 10**11
    factor_two = upper_power(2, F(4, 5) - beta)
    leading_power = upper_power(n, (beta-F(3, 5))/2)
    lower_power = upper_power(n, beta-F(4, 5))
    e1 = F(46,225)*factor_two*leading_power + F(23,30)*factor_two*lower_power
    e2 = (F(44,225)/RHO*leading_power + F(22,15)/RHO**2*lower_power
          + F(88,225)*upper_power(n,-F(3,10)) + F(44,15)*upper_power(n,-F(4,5)))
    assert F(21,50)+e1+e2 < F(2,3)
    print("C=1 beta=11/20 at 10^11: E1 <=", ceil_decimal(e1), "E2 <=", ceil_decimal(e2))
    print("beta | certified n0 | upper total | extra n=2 mod 4 cases")
    for beta in [F(55, 100), F(56, 100), F(57, 100), F(58, 100), F(59, 100)]:
        for decade in range(1, 201):
            n = 10**decade
            bound, _ = envelope(n, beta)
            if cutoff_condition(n, beta) and bound < F(2, 3):
                print(beta, f"10^{decade}", ceil_decimal(bound), extra_cases(n), sep=" | ")
                break
        else:
            raise AssertionError("No threshold found through 10^200")
    # At beta=3/5,C=1 the AM-GM lower bound on the leading pair alone
    # exceeds the remaining budget for every positive real P.
    a_lower = F(23, 225)  # 2**(1/5)>1
    d = F(88, 225)
    margin = F(37, 150)
    assert 4*a_lower*d > margin**2
    print("beta=3/5,C=1: exact AM-GM obstruction verified for this budget")


if __name__ == "__main__":
    main()

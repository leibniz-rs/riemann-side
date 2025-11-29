import math

def calculate_kxi(C_vk, B_vk, alpha, c):
    """
    Calculate K_xi bound based on Riemann-active.txt Lemma 12 / Appendix B logic.

    K_xi ~ C_alpha * Sum(4^-k * nu_k)
    nu_k <= C_vk * (2^k * L * logT)^1 * (log T)^B_vk  (Conservative linear approx)
    Actually, nu_k comes from N(sigma, T).

    Let's use the formula from the proof of Lemma 12:
    Sum_{k>=1} 4^-k * nu_k <= a1 * L * logT * Sum 2^-k + a2 * logT * Sum 4^-k

    On Whitney scale, L = c / logT.
    So L * logT = c.

    Term 1: a1 * c * (1)  (Sum 2^-k = 1)
    Term 2: a2 * logT * (1/3) (Sum 4^-k = 1/3) -- This term grows with logT!

    Wait, the manuscript says:
    "nu_k << 2^k L log T + log T"
    "Sum ... << L log T + 1"
    "On Whitney scale L = c/log T this is << 1."

    The "1" term comes from the "log T" part of the density.
    If nu_k has a constant term (log T), then Sum 4^-k * log T is NOT O(1) * |I|.
    |I| = 2L = 2c / log T.
    So we need (Sum) / |I| to be bounded.

    (a1 * c + a2 * log T) / (2 * c / log T)
    = a1 * log T / 2 + a2 * (log T)^2 / (2c).

    This DIVERGES as T -> infinity!

    Unless nu_k is SMALLER.
    The density N(sigma, T) is for the whole rectangle.
    nu_k is the count in an annulus.

    Let's check the "far field" integral.
    Integral_{Q} |sum 1/(s-rho)|^2

    The manuscript claims K_xi is finite.
    This implies the "log T" term must be suppressed or handled.

    Let's look at Lemma 12 proof again:
    "Sum 4^-k nu_k << L log T + 1"
    "On Whitney scale ... this is << 1."

    Wait, 1 vs |I|.
    |I| = 2L = 2c/log T.
    So 1 / |I| = log T / (2c).
    So the energy density diverges as log T?

    UNLESS the "1" term is absent or handled differently.

    Actually, for Carleson measure condition, we need:
    Int_{Q(I)} |grad U|^2 sigma <= K * |I|.

    If the integral is O(1), and |I| is small, then K is LARGE.

    The only way K_xi is small (and constant) is if the Integral scales as |I|.
    Integral ~ |I|.

    If nu_k ~ log T (constant density per unit height),
    then Sum 4^-k nu_k ~ log T.
    Then Integral ~ log T.
    But |I| ~ 1/log T.
    So Ratio ~ (log T)^2.

    This suggests the standard VK bound N(sigma, T) ~ T is NOT enough for small intervals if the zeros are uniformly distributed.

    However, N(sigma, T+H) - N(sigma, T) for small H?
    If H = L, we expect N(sigma, T+L) - N(sigma, T) to be small.

    Standard bound: N(T+H) - N(T) << H log T.
    So nu_k (annulus height ~ 2^k L)
    nu_k << (2^k L) * log T.

    Then Sum 4^-k nu_k << Sum 4^-k * 2^k * L * log T
    = L * log T * Sum 2^-k
    = L * log T.

    Since L = c / log T, this is:
    c * (c/log T * log T) = c.

    So the integral is O(c).
    The interval length |I| = 2L = 2c / log T.

    Ratio = O(c) / (2c / log T) ~ log T.

    THIS IS A PROBLEM. The energy *density* seems to grow with log T.
    The manuscript claims K_xi is finite (constant).

    Is there a factor of 1/log T missing in the Energy calculation?

    Let's assume the manuscript is correct and I'm missing a scaling factor.
    Or, the manuscript relies on the "geometric decay" killing the log T.

    Let's calculate the Ratio explicitly.

    Ratio = (Sum 4^-k * nu_k) / |I|
    Using nu_k = A * (2^k L) * log T (approx density)
    Sum = A * L * log T * Sum(2^-k) = A * L * log T.
    Ratio = (A * L * log T) / (2L) = A * log T / 2.

    This still grows with log T.

    UNLESS "Carleson energy" is defined differently or I'm misinterpreting the sum.

    Wait, Lemma 12 says:
    "Sum ... << L log T + 1"
    "On Whitney scale ... this is << 1."

    "This is << 1" means the INTEGRAL is bounded by a constant.
    But to be a Carleson measure, the integral must be bounded by K * |I|.
    If Integral ~ 1 and |I| ~ 0 (small), then K ~ 1/|I| -> infinity.

    ERROR CANDIDATE 1: The manuscript might be claiming the integral is O(|I|), but the math suggests O(1).

    Let's verify this with the script.
    """

    # Model parameters
    T = 10**10 # Large T
    logT = math.log(math.sqrt(1+T**2))
    L = c / logT

    # Annular counts
    # nu_k approx C_vk * (height) * log T * decay?
    # VK bound: N(sigma, T) <= C * T^(1-k)
    # Density n(t) ~ d/dT N ~ C * T^-k * log T?

    # Let's use the "short interval" estimate:
    # N(T+H) - N(T) <= A1 * H * log T
    # So nu_k = A1 * (2^k L) * log T

    A1 = C_vk # Assume C_vk controls the density constant

    total_energy_sum = 0
    for k in range(1, 20):
        height = 2**k * L
        nu_k = A1 * height * logT
        term = (1.0 / 4**k) * nu_k
        total_energy_sum += term

    # Resulting K_xi approx
    # Integral approx C_alpha * total_energy_sum
    # Divided by |I| = 2L

    # C_alpha factor from Lemma 11 proof (diagonal + off-diagonal)
    # C_diag = 4/3 * alpha^3
    # C_off approx... let's take C_alpha = 10 for a conservative check
    C_alpha = 10.0

    integral = C_alpha * total_energy_sum
    interval_len = 2 * L

    K_xi = integral / interval_len

    print(f"Params: C_vk={C_vk}, c={c}, T={T:.1e}")
    print(f"L = {L:.2e}")
    print(f"Integral Sum = {total_energy_sum:.2e}")
    print(f"Interval Len = {interval_len:.2e}")
    print(f"Ratio (K_xi) = {K_xi:.2f}")

    return K_xi

# Test with manuscript values
print("--- Checking Manuscript Claim ---")
calculate_kxi(C_vk=1.0, B_vk=0, alpha=1.5, c=0.1) # Assuming ideal C_vk=1
calculate_kxi(C_vk=1000.0, B_vk=5, alpha=1.5, c=0.1) # Ivic constants

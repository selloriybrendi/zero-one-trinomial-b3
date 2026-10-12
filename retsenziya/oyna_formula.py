"""oyna_formula.py — asosiy shox q_N ning sinf-formulasi (barcha k uchun qo'l bilan chiqarilgan) va uning FLINT tekshiruvi.
Asosiy shox r_n: n<k: [3|n]; n=k: 1; k<n<=2k: 0 agar n ≡ −k (mod 3), aks holda 1; n>2k: 1.
GF: q_N = Σ_{p>=0} (−1)^p Σ_i C(p+i,p)(−a)^i r_{N−pk−3i}. M = N − pk ning sinfi bo'yicha r ning tayanchi:
  M ≡ 0      : r_m = 1 barcha m>=0 (sinf 0)          → L = M/3
  M ≡ k      : r_m = 1 ⟺ m >= k                       → L = (M−k)/3     (M < k ⇒ had yo'q)
  M ≡ −k     : r_m = 1 ⟺ m >= 2k+3                    → L = (M−2k−3)/3  (M < 2k+3 ⇒ had yo'q)
Demak q_N = Σ_{p: L_p>=0} (−1)^p T_{L_p}[(1+a)^{−(p+1)}]   (T_L — daraja-L kesmasi).   ← AYNAN, k ga cheklovsiz."""
import sys
from math import comb
from flint import fmpq_poly
A = fmpq_poly([0, 1]); NOL = fmpq_poly([0])
def T(L, p):
    return fmpq_poly([(-1) ** i * comb(p + i, p) for i in range(L + 1)])
def L_p(N, p, k):
    M = N - p * k
    if M < 0: return None
    s = M % 3
    if s == 0: return M // 3
    if s == k % 3: return (M - k) // 3 if M >= k else None
    return (M - 2 * k - 3) // 3 if M >= 2 * k + 3 else None
def formula(N, k):
    v = NOL
    for p in range(N // k + 1):
        L = L_p(N, p, k)
        if L is not None: v += (-1) ** p * T(L, p)
    return v
def q_asosiy(k, N):
    q = []
    for n in range(N + 1):
        if n < k: r = 1 if n % 3 == 0 else 0
        elif n == k: r = 1
        else: r = 0 if (n <= 2 * k and (n + k) % 3 == 0) else 1
        q.append(fmpq_poly([r]) - A * (q[n - 3] if n >= 3 else NOL) - (q[n - k] if n >= k else NOL))
    return q
if __name__ == "__main__":
    k1, k2 = int(sys.argv[1]), int(sys.argv[2]); jami = buz = 0
    for k in range(k1, k2 + 1):
        if k % 3 == 0: continue
        q = q_asosiy(k, 5 * k + 12)
        for N in range(5 * k + 13):
            jami += 1
            if q[N] != formula(N, k): buz += 1; print("BUZILISH", k, N) if buz < 5 else None
    print(f"k={k1}..{k2} (k≢0): {jami} ta q_N tekshirildi · buzilish {buz}")

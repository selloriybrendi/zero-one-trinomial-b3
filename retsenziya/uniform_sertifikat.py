"""uniform_sertifikat.py — b=3, BARCHA k >= K (k≢0 mod 3), a ∈ (0, 1/2] uchun bitta qat'iy sertifikat.
Asos (oyna_formula.py, qo'l bilan chiqarilgan): q_N = Σ_p (−1)^p T_{L_p}[(1+a)^{−(p+1)}].
N = jk + m (0<=m<k). L_p = (αk + m − β)/3; α = j−p−{0,1,2} (sinf 0 / k / −k), β = {0,0,3}.
  α = 0  → "tirik" had: L = (m−β)/3, k ga bog'liq EMAS — aniq ko'phad.
  α >= 1 → "mayda" had: T_L = (1+a)^{−(p+1)} − tail, |tail| <= C(p+L+1,p)·a^{L+1}, L >= (k−3)/3 (Leibniz: a<=1/2, L>=4).
  α < 0  → had yo'q.
Shuning uchun har (j, m) "tur" qiymati k ga faqat k mod 3 orqali bog'liq + xato <= C·a^{λ}. m > M0 da tirik dumlar ham chegaralanadi.
Tekshiruv (har a-oraliq I uchun, arb bilan qat'iy): asosiy shox bo'ylab n = k, k+1, …, 5k+12:
  S1: n erkin to'plamda bo'lmasa (k<n<=2k, n≡−k), q_{n−3} yoki q_{n−k} qat'iy MUSBAT (⇒ r_n=0 imkonsiz, r_n=1 majbur);
  S2: biror n da q_n qat'iy MANFIY (o'lim) topilsin;
  S3: noaniq (AMB) qiymat 0 bo'lishi mumkin deb hisoblanadi (eng yomon holat) — S1 ga sherik bo'la olmaydi.
Yurgizish: ~/arsenal-venv/bin/python retsenziya/uniform_sertifikat.py [K] [M0]"""
import sys
from math import comb
from flint import fmpq_poly, arb, arb_poly, fmpq
K = int(sys.argv[1]) if len(sys.argv) > 1 else 151
M0 = int(sys.argv[2]) if len(sys.argv) > 2 else 60
A = fmpq_poly([0, 1]); BIR = fmpq_poly([1]); NOL = fmpq_poly([0])
P1 = BIR + A
def T(L, p): return fmpq_poly([(-1) ** i * comb(p + i, p) for i in range(L + 1)])
LMAYDA = (K - 3) // 3                     # mayda hadlar uchun eng kichik L
L0 = (M0 + 1 - 3) // 3                    # katta-m turlarida tirik dumlar uchun eng kichik L

def tur(c, j, m=None, katta_rho=None):
    """(sur'at N(a) [fmpq_poly], xatolar [(C, λ)]) — qiymat = N/(1+a)^6 + E, |E| <= Σ C·a^λ."""
    num = NOL; xato = []
    for p in range(j + 1):
        mm = m if m is not None else katta_rho
        cls = ((j - p) * c + mm) % 3
        if cls == 0: alfa, beta = j - p, 0
        elif cls == c: alfa, beta = j - p - 1, 0
        else: alfa, beta = j - p - 2, 3
        if alfa < 0: continue
        if alfa >= 1:                       # mayda: to'liq ratsional + Leibniz dum
            num += (-1) ** p * P1 ** (5 - p); xato.append((comb(p + LMAYDA + 1, p), LMAYDA + 1)); continue
        if m is not None:                   # tirik, aniq
            if m - beta < 0: continue
            L = (m - beta) // 3
            num += (-1) ** p * T(L, p) * P1 ** 6
        else:                               # tirik, katta m: to'liq ratsional + dum
            num += (-1) ** p * P1 ** (5 - p); xato.append((comb(p + L0 + 1, p), L0 + 1))
    return num, xato

def belgi(t, lo, hi):
    """'POS' / 'NEG' / 'AMB' / 'ZERO' — I=[lo,hi] da qat'iy (arb)."""
    num, xato = t
    if num == 0 and not xato: return "ZERO"
    if num == 0: return "AMB"
    co = [num[i] for i in range(num.degree() + 1)]
    v = next(i for i, x in enumerate(co) if x != 0)
    W = fmpq_poly(co[v:])
    I = arb(fmpq(lo.numerator, lo.denominator)).union(arb(fmpq(hi.numerator, hi.denominator)))
    w = arb_poly(W)(I)
    h = arb(fmpq(hi.numerator, hi.denominator))
    e = arb(0)
    for C, lam in xato:
        if lam <= v: return "AMB"
        e += arb(C) * h ** (lam - v)
    e *= (1 + h) ** 6
    if w - e > 0: return "POS"
    if w + e < 0: return "NEG"
    return "AMB"

def yurish(c, lo, hi, kesh):
    """Asosiy shox bo'ylab yurish. Qaytaradi (ok, sabab, o'lim_turi)."""
    def B(key):
        if key not in kesh:
            j, x, katta = key
            kesh[key] = belgi(tur(c, j, None if katta else x, x if katta else None), lo, hi)
        return kesh[key]
    def turi(j, m):          # (j, m) → kesh kaliti; m >= k bo'lsa keyingi oyna; m > M0 → katta tur
        return (j, m, False) if m <= M0 else (j, m % 3, True)
    def erkin(j, m):         # k < n <= 2k, n ≡ −k
        return (j == 1 and m >= 1 and (c + m) % 3 == (-c) % 3) or (j == 2 and m == 0)
    pozitsiyalar = []
    for j in range(1, 6):
        mmax = 12 if j == 5 else None
        for m in range(0, (M0 if mmax is None else 12) + 1): pozitsiyalar.append((j, m, False))
        if mmax is None:
            for m in range(M0 + 1, M0 + 4): pozitsiyalar.append((j, m, False))      # chegara
            for rho in range(3): pozitsiyalar.append((j, rho, True))                 # umumiy katta
    for j, x, umumiy in pozitsiyalar:
        if umumiy:
            m_s = None; key_n = (j, x, True)
            key3 = (j, (x - 3) % 3, True); keyk = (j - 1, x, True)
            is_free = erkin(j, M0 + 3 + ((x - (M0 + 3)) % 3) if True else 0)
        else:
            m = x; key_n = turi(j, m)
            key3 = turi(j, m - 3) if m >= 3 else turi(j - 1, 10 ** 6 + ((c + m - 3) % 3) * 0 + 0) if False else None
            if m >= 3: key3 = turi(j, m - 3)
            else: key3 = (j - 1, (c + m - 3) % 3, True)          # oldingi oyna oxiri: m' = k + m − 3 (katta)
            keyk = turi(j - 1, m)
            is_free = erkin(j, m)
        if not is_free:
            s3, sk = B(key3), B(keyk)
            if not (s3 == "POS" or sk == "POS"):
                return False, f"S1 yiqildi n=({j},{x}{',katta' if umumiy else ''}) sherik: {s3}/{sk}", None
        sn = B(key_n)
        if sn == "NEG": return True, "o'lim", (j, x, umumiy)
    return False, "o'lim topilmadi", None

def sertifikat(c, bo=64, chuqur=40):
    from fractions import Fraction as F
    navbat = [(F(i, 2 * bo), F(i + 1, 2 * bo), 0) for i in range(bo)]
    olim = {}; yiq = []; soni = 0
    while navbat:
        lo, hi, d = navbat.pop()
        ok, sabab, ot = yurish(c, lo, hi, {}); soni += 1
        if ok: olim[ot] = olim.get(ot, 0) + 1; continue
        if d >= chuqur: yiq.append((float(lo), float(hi), sabab)); continue
        mid = (lo + hi) / 2; navbat += [(lo, mid, d + 1), (mid, hi, d + 1)]
    return soni, olim, yiq

if __name__ == "__main__":
    for c in (1, 2):
        soni, olim, yiq = sertifikat(c)
        print(f"k ≡ {c} (mod 3), K={K}, M0={M0}: tekshirilgan oraliq {soni} · yiqilgan {len(yiq)} · o'lim turlari {dict(sorted(olim.items()))}")
        for y in yiq[:6]: print("   YIQILDI:", y)

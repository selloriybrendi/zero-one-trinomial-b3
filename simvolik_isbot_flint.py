"""simvolik_isbot_flint.py — simvolik_isbot.py v2 ning FLINT+PARI dvigateli (FUNDAMENT M31 Sage/PARI yo'lagi).
Mantiq AYNAN v2: q_n(a) = r_n − a q_{n−b} − q_{n−k}, r=0 faqat q_{n−b}≡q_{n−k}≡0 da; r=1 shoxida ishora (lo,hi) da
ildiz-izolyatsiya bilan bo'linadi. Farq faqat dvigatelda:
  ko'phad arifmetikasi — python-flint fmpq_poly (C, aniq ratsional)
  ildiz sanash         — PARI polsturm (aniq, ratsional chegaralar) — Sturm sympy'dagi bilan bir xil ma'no
  ildiz joylashuvi     — PARI polrootsreal (taxminiy) → ratsional 2^-40 qutilar → polsturm bilan AYNAN tasdiqlanadi;
                         tasdiq o'tmasa aniq ikkiga bo'lish (fallback) — natija har doim aniq.
Versiyalar (2026-10-11, o'lchovlar ISH-JURNAL.md da):
  v3 — takror PARI o'tkazishlari tuple(coeffs) kalit bilan keshlanadi (12–17% tez)
  v4 — bolaklar(): har quti uchun Sturm 1 marta, oraliq tekshiruvlari olib tashlandi ((9,13) 357168 → 327773 chaqiriq)
  v5 — arb shar-elak (ARB_ELAK=1): ball 0 ni qamramasa Sturm chaqirilmaydi ((9,13) → 134208 chaqiriq, 3.34 → 1.72 s)
  GCD_TEKSHIR=1 — izolyatsiyalangan a nuqtalari nuqtaviy.py bilan aniq tekshiriladi (M16 #5)
Yurgizish: ~/arsenal-venv/bin/python simvolik_isbot_flint.py b k [N] [lo hi]"""

import json
import sys
import time
from fractions import Fraction
from flint import fmpq_poly, fmpq, arb, arb_poly
import cypari2

pari = cypari2.Pari()
pari.allocatemem(256 * 1024 * 1024)
sys.setrecursionlimit(100000)
EPS = Fraction(1, 10**9)
D = 1 << 40
import os

GCD_TEKSHIR = os.environ.get("GCD_TEKSHIR") == "1"
ARB_ELAK = os.environ.get("ARB_ELAK", "1") == "1"
ELAK = [0]


def _fq(x):
    return fmpq(x.numerator, x.denominator)


X = fmpq_poly([0, 1])
NOL = fmpq_poly([0])
BIR = fmpq_poly([1])


def fr(x):  # fmpq → Fraction
    return Fraction(int(x.p), int(x.q))


# v3 (2026-10-11): takror PARI o'tkazishlari keshlanadi (M55). Profil: (7,15) da 68565 o'tkazishdan 5428 tasi noyob edi.
_PR = {}
_PP = {}


def pr(f):  # Fraction → pari ratsional (keshlangan)
    v = _PR.get(f)
    if v is None:
        if len(_PR) > 200000:
            _PR.clear()
        v = _PR[f] = pari(f.numerator) / pari(f.denominator)
    return v


def to_pari(
    P,
):  # fmpq_poly → pari ko'phad (keshlangan; maxrajni tashlash ishorani o'zgartirmaydi, q>0)
    c = P.p.coeffs()
    k = tuple(
        c
    )  # arzon kalit: coeffs() ~5 mks, str(P) ~62 mks (o'lchangan) — str kalit konvertatsiyadan qimmat edi
    v = _PP.get(k)
    if v is None:
        if len(_PP) > 50000:
            _PP.clear()
        v = _PP[k] = pari.Polrev([int(x) for x in c], "a")
    return v


def sturm(Pp, l, h):
    return int(pari.polsturm(Pp, [pr(l), pr(h)]))


def ishora(P, l, h):
    v = P(fmpq((l + h).numerator, (l + h).denominator * 2))
    return "+" if v > 0 else ("-" if v < 0 else "?")


def _nol(P, x):
    return P(fmpq(x.numerator, x.denominator)) == 0


def sturm_ochiq(P, Pp, l, h, LO, HI):
    """[l,h] dagi ildizlar soni, (LO,HI) OCHIQ oraliq chegaralaridagi ildizlar sanalmaydi (a=0, a=1 chetlanadi — v2 sympy intervals bilan bir xil)."""
    n = sturm(Pp, l, h)
    if l == LO and _nol(P, LO):
        n -= 1
    if h == HI and _nol(P, HI):
        n -= 1
    return n


def bolaklar(P, lo, hi):
    """(lo,hi) → [(l,h,ishora)] — v2 bilan bir xil ma'no: ildizsiz bo'lak '+'/'-', ildizli tor bo'lak (eni<EPS) '?'."""
    # v5 (2026-10-11): arb shar-elak — [lo,hi] ustida P ning qat'iy ball-bahosi 0 ni o'z ichiga olmasa, ildiz YO'Q (aniq, arb
    # yaxlitlash xatosini ham qamraydi) → Sturm chaqirilmaydi. Faqat shar 0 ni qamrasa Sturm (aniq) ishga tushadi.
    if ARB_ELAK:
        v = arb_poly(P)(arb(_fq(lo)).union(arb(_fq(hi))))
        if not v.contains(0):
            ELAK[0] += 1
            return [(lo, hi, "+" if v > 0 else "-")]
    Pp = to_pari(P)
    n = sturm_ochiq(P, Pp, lo, hi, lo, hi)
    if n == 0:
        return [(lo, hi, ishora(P, lo, hi))]
    qutilar = []
    for r in pari.polrootsreal(Pp, [pr(lo), pr(hi)]):
        x = (
            Fraction(str(r))
            if "E" not in str(r) and "e" not in str(r)
            else Fraction(float(r))
        )
        l = Fraction(int((x * D).__floor__()) - 1, D)
        h = Fraction(int((x * D).__floor__()) + 2, D)
        l, h = max(l, lo), min(h, hi)
        if h > l:
            qutilar.append([l, h])
    qutilar.sort()
    birl = []
    for l, h in qutilar:
        if birl and l <= birl[-1][1]:
            birl[-1][1] = max(birl[-1][1], h)
        else:
            birl.append([l, h])
    # v4 (2026-10-11): har quti uchun Sturm BIR marta (oldin filtr + yig'indi = 2 marta) va oraliq (gap) tekshiruvlari olib tashlandi:
    # qutilar yopiq, kesishmaydi va (lo,hi) ichida; ularning ildiz sonlari yig'indisi = n bo'lsa, n ta ildizning hammasi qutilarda,
    # demak oraliqlarning ochiq ichki qismida ildiz YO'Q — oraliq tekshiruvi matematik ortiqcha edi. Tugun boshiga 3r+2 → r+1 chaqiriq.
    sanoq = [sturm_ochiq(P, Pp, l, h, lo, hi) for l, h in birl]
    birl = [
        q for q, c in zip(birl, sanoq) if c > 0
    ]  # chegara ildizining qutisi tashlanadi
    ok = sum(sanoq) == n
    out = []
    x = lo
    for l, h in birl:
        if x < l:
            out.append((x, l, "?"))
        out.append((l, h, "?"))
        x = h
    if x < hi:
        out.append((x, hi, "?"))
    if ok:
        return [
            (l, h, "?") if [l, h] in birl else (l, h, ishora(P, l, h))
            for l, h, _ in out
        ]
    return _bolak_bisect(P, Pp, lo, hi, lo, hi)  # fallback: aniq ikkiga bo'lish


def _bolak_bisect(P, Pp, lo, hi, LO, HI):
    n = sturm_ochiq(P, Pp, lo, hi, LO, HI)
    if n == 0:
        return [(lo, hi, ishora(P, lo, hi))]
    if hi - lo < EPS:
        return [(lo, hi, "?")]
    m = (lo + hi) / 2
    return _bolak_bisect(P, Pp, lo, m, LO, HI) + _bolak_bisect(P, Pp, m, hi, LO, HI)


def _ichki(g, lo, hi):
    """g ning [lo,hi] (yopiq; faqat global 0 va 1 chiqariladi) dagi ildizlari soni."""
    c = sturm(to_pari(g), lo, hi)
    if lo == 0 and _nol(g, lo):
        c -= 1
    if hi == 1 and _nol(g, hi):
        c -= 1
    return c


def _nuqta_yig(qb, qk, lo, hi, n, st):
    """r=0 shoxi faqat qb(a)=qk(a)=0 da ochiladi. Ko'phad sifatida ikkalasi nol bo'lmasa ham, umumiy ildizlarda
    (izolyatsiyalangan a) ochiladi — shu a larni (minimal ko'phad, oraliq) bilan yig'amiz; keyin nuqtaviy aniq DFS."""
    if qb == NOL and qk == NOL:
        return
    g = qk if qb == NOL else (qb if qk == NOL else qb.gcd(qk))
    if g.degree() < 1 or _ichki(g, lo, hi) == 0:
        return
    for f, _ in pari.factor(to_pari(g)).mattranspose():
        fq = fmpq_poly([int(c) for c in pari.Vecrev(f)])
        if fq.degree() >= 1 and _ichki(fq, lo, hi) > 0:
            st.setdefault("nuqta", []).append(
                (n, tuple(int(c) for c in pari.Vecrev(f)), lo, hi)
            )


def dfs(lo, hi, b, k, N, q, n, st):
    if n > st["maks"]:
        st["maks"] = n
    if n > N:
        st["tirik"].append((lo, hi))
        return False
    qb = q[n - b] if n >= b else NOL
    qk = q[n - k] if n >= k else NOL
    if n > k and all(x == NOL for x in q[n - k : n]) and q[n - k - 1] == BIR:
        st["qarshi"].append((lo, hi, n))
        return False
    oldi = True
    if GCD_TEKSHIR:
        _nuqta_yig(qb, qk, lo, hi, n, st)
    if qb == NOL and qk == NOL:
        q.append(NOL)
        oldi &= dfs(lo, hi, b, k, N, q, n + 1, st)
        q.pop()
    qn = BIR - X * qb - qk
    if (
        GCD_TEKSHIR and qn != NOL
    ):  # bo'lak chegarasiga aynan tushgan ildiz: ochiq bo'laklar uni tekshirmaydi → nuqtaviy
        for e in (lo, hi):
            if 0 < e < 1 and _nol(qn, e):
                st.setdefault("nuqta", []).append(
                    (n, (-e.numerator, e.denominator), e, e)
                )
    if qn == NOL:
        q.append(qn)
        oldi &= dfs(lo, hi, b, k, N, q, n + 1, st)
        q.pop()
        return oldi
    if qn.degree() == 0:
        if qn[0] > 0:
            q.append(qn)
            oldi &= dfs(lo, hi, b, k, N, q, n + 1, st)
            q.pop()
        else:
            st["barg"] += 1
            st["olim"][n] = st["olim"].get(n, 0) + 1
        return oldi
    for l, h, s in bolaklar(qn, lo, hi):
        if s == "-":
            st["barg"] += 1
            st["olim"][n] = st["olim"].get(n, 0) + 1
        else:
            if (l, h) != (lo, hi):
                st["bolak"] += 1
            q.append(qn)
            oldi &= dfs(l, h, b, k, N, q, n + 1, st)
            q.pop()
    return oldi


def isbot(b, k, N=400, lo=Fraction(0), hi=Fraction(1)):
    st = {"maks": 0, "qarshi": [], "tirik": [], "barg": 0, "olim": {}, "bolak": 0}
    t0 = time.time()
    ok = (
        dfs(Fraction(lo), Fraction(hi), b, k, N, [BIR], 1, st)
        and not st["tirik"]
        and not st["qarshi"]
    )
    return {
        "b": b,
        "k": k,
        "N": N,
        "lo": str(lo),
        "hi": str(hi),
        "isbot": ok,
        "dvigatel": "flint+pari",
        "a_bolaklar": st["bolak"],
        "maks_chuqurlik": st["maks"],
        "barglar": st["barg"],
        "olim_nuqtalari": dict(sorted(st["olim"].items())),
        "tirik": [(str(x), str(y)) for x, y in st["tirik"][:5]],
        "qarshi": [(str(x), str(y), n) for x, y, n in st["qarshi"][:5]],
        "vaqt_s": round(time.time() - t0, 2),
        "nuqta_bayroq": len(st.get("nuqta", [])),
    }, st


if __name__ == "__main__":
    b, k = int(sys.argv[1]), int(sys.argv[2])
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    lo, hi = (
        (Fraction(sys.argv[4]), Fraction(sys.argv[5]))
        if len(sys.argv) > 5
        else (Fraction(0), Fraction(1))
    )
    r, st = isbot(b, k, N, lo, hi)
    if GCD_TEKSHIR:
        import nuqtaviy

        r["nuqtaviy"] = nuqtaviy.tekshir(b, k, N, st.get("nuqta", []))
        r["isbot_toliq"] = r["isbot"] and r["nuqtaviy"]["hammasi_oldi"]
    print(json.dumps(r, ensure_ascii=False))
    nom = (
        f"sertifikat_{b}_{k}.json"
        if (lo, hi) == (0, 1)
        else f"sertifikat_{b}_{k}_{lo.numerator}-{lo.denominator}_{hi.numerator}-{hi.denominator}.json"
    )
    json.dump(
        r, open(nom.replace(".json", "_flint.json"), "w"), ensure_ascii=False, indent=1
    )

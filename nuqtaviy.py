"""nuqtaviy.py — izolyatsiyalangan a nuqtalarida (qb(a)=qk(a)=0 bo'lgan algebraik sonlar) ANIQ nuqtaviy DFS.
Arifmetika Q(α) da: element = fmpq_poly mod f (f — α ning minimal ko'phadi), ishora = α izolyatsiya oralig'ini
Sturm bilan toraytirib aniqlanadi. Shox faqat q_{n-b} = q_{n-k} = 0 (aniq) bo'lganda ikkiga bo'linadi."""
import sys
from fractions import Fraction
from flint import fmpq_poly, fmpq
import simvolik_isbot_flint as S
sys.setrecursionlimit(100000)

class Nuqta:
    def __init__(self, f, lo, hi):
        self.f = fmpq_poly(list(f)); self.lo, self.hi = lo, hi
    def ishora(self, p):
        p = p % self.f
        if p == S.NOL: return 0
        if self.lo == self.hi:
            v = p(fmpq(self.lo.numerator, self.lo.denominator)); return 1 if v > 0 else (-1 if v < 0 else 0)
        while S.sturm(S.to_pari(p), self.lo, self.hi) > 0:  # p ning ildizi α ning oralig'ida — toraytir
            m = (self.lo + self.hi) / 2
            if S._nol(self.f, m): self.lo = self.hi = m; return self.ishora(p)
            if S.sturm(S.to_pari(self.f), self.lo, m) > 0: self.hi = m
            else: self.lo = m
            if self.hi - self.lo < Fraction(1, 2**400): raise RuntimeError("toraytirish chegarasi")
        mid = (self.lo + self.hi) / 2
        v = p(fmpq(mid.numerator, mid.denominator))
        return 1 if v > 0 else (-1 if v < 0 else 0)

def ajrat(f, lo, hi):
    """f ning [lo,hi] dagi har ildizi uchun alohida izolyatsiya oralig'i (ratsional ildiz → (r,r))."""
    fq = fmpq_poly(list(f)); out = []
    if fq.degree() == 1:
        r = -Fraction(int(fq[0].p), int(fq[0].q)) / Fraction(int(fq[1].p), int(fq[1].q))
        return [(r, r)] if lo <= r <= hi and 0 < r < 1 else []
    navbat = [(lo, hi)]
    while navbat:
        l, h = navbat.pop(); c = S._ichki(fq, l, h)
        if c == 0: continue
        if c == 1: out.append((l, h)); continue
        m = (l + h) / 2; navbat += [(l, m), (m, h)]
    return out

def dfs_nuqta(al, b, k, N, q, n, st):
    if n > st["maks"]: st["maks"] = n
    if n > N: st["tirik"] += 1; return False
    qb = q[n - b] if n >= b else S.NOL; qk = q[n - k] if n >= k else S.NOL
    if n > k and all(al.ishora(x) == 0 for x in q[n - k:n]) and al.ishora(q[n - k - 1] - S.BIR) == 0:
        st["qarshi"] += 1; return False
    oldi = True
    if al.ishora(qb) == 0 and al.ishora(qk) == 0:
        st["shox"] += 1; q.append(S.NOL); oldi &= dfs_nuqta(al, b, k, N, q, n + 1, st); q.pop()
    qn = (S.BIR - S.X * qb - qk) % al.f
    if al.ishora(qn) < 0: st["barg"] += 1; return oldi
    q.append(qn); oldi &= dfs_nuqta(al, b, k, N, q, n + 1, st); q.pop()
    return oldi

def tekshir(b, k, N, nuqtalar):
    """nuqtalar: [(n, f_koeff, lo, hi)] → takrorsiz algebraik nuqtalar bo'yicha nuqtaviy DFS."""
    noyob = []
    for _, f, lo, hi in nuqtalar:
        for l, h in ajrat(f, lo, hi):
            if not any(g == f and not (h < l2 or h2 < l) for g, l2, h2 in noyob): noyob.append((f, l, h))
    nat = {"nuqta_soni": len(noyob), "oldi": 0, "tirik": 0, "maks_chuqurlik": 0, "shox": 0, "namuna": []}
    for f, l, h in noyob:
        al = Nuqta(f, l, h)
        st = {"maks": 0, "tirik": 0, "qarshi": 0, "barg": 0, "shox": 0}
        ok = dfs_nuqta(al, b, k, N, [S.BIR], 1, st) and st["tirik"] == 0 and st["qarshi"] == 0
        nat["oldi" if ok else "tirik"] += 1; nat["maks_chuqurlik"] = max(nat["maks_chuqurlik"], st["maks"]); nat["shox"] += st["shox"]
        if len(nat["namuna"]) < 3: nat["namuna"].append({"f": list(f), "oraliq": [str(l), str(h)], "oldi": ok, "chuqurlik": st["maks"], "shox": st["shox"]})
    nat["hammasi_oldi"] = nat["tirik"] == 0
    return nat

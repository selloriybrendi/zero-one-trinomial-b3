"""ildiz_nuqta.py — A yo'l: b=3, k>=151 da asosiy shox o'lim ko'phadlarining (0,1/2] dagi HAR ildizida aniq nuqtaviy DFS.
O'lim ko'phadlari: q_n (asosiy shox), n in {3k+12, 4k+15, 5k+3, 5k+12}. Ildizda shu o'lim yo'q (q_n = 0), shox keyinroq
o'lishi kerak. nuqtaviy.dfs_nuqta Q(alpha) da HAMMA shoxni (r=0 imkoni ham) aniq kuzatadi.
Ishlatish: python ildiz_nuqta.py k [N]   (N sukut 5k+60)."""
import sys, json, time, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from fractions import Fraction
from flint import fmpq_poly
import simvolik_isbot_flint as S
import nuqtaviy as NQ
from cypari2 import Pari
pari = S.pari

def asosiy(k, M):
    X = fmpq_poly([0, 1]); q = [fmpq_poly([1])]
    for n in range(1, M + 1):
        if n < k: r = 1 if n % 3 == 0 else 0
        elif n == k: r = 1
        elif n <= 2 * k: r = 0 if (n + k) % 3 == 0 else 1
        else: r = 1
        qb = q[n - 3] if n >= 3 else fmpq_poly([])
        qk = q[n - k] if n >= k else fmpq_poly([])
        q.append(fmpq_poly([r]) - X * qb - qk)
    return q

def main(k, N):
    t0 = time.time()
    D = [3 * k + 12, 4 * k + 15, 5 * k + 3, 5 * k + 12]
    q = asosiy(k, max(D))
    nuqtalar = []
    # HAMMA q_n (n <= 5k+12) ning (0,1/2] dagi ildizlari — o'lim ko'phadlari va sheriklar ham (agent 6 nuqtasi shu to'plamda)
    for n in range(1, max(D) + 1):
        if q[n].degree() < 1 or S._ichki(q[n], Fraction(0), Fraction(1, 2)) == 0: continue
        for f, _ in pari.factor(S.to_pari(q[n])).mattranspose():
            c = tuple(int(x) for x in pari.Vecrev(f))
            if len(c) >= 2:
                for l, h in NQ.ajrat(c, Fraction(0), Fraction(1, 2)):
                    if h > 0: nuqtalar.append((n, c, l, h))
    ildizlar = []
    for n, c, l, h in nuqtalar:
        fq = fmpq_poly(list(c))
        while h - l > Fraction(1, 10**14):
            m = (l + h) / 2
            if S._nol(fq, m): l = h = m; break
            if S._ichki(fq, l, m) > 0: h = m
            else: l = m
        ildizlar.append((n, float((l + h) / 2), len(c) - 1))
    nat = NQ.tekshir(3, k, N, nuqtalar)
    print(json.dumps({"k": k, "N": N, "ildiz_soni": len(nuqtalar),
        "ildizlar": sorted(set((round(x, 10), n) for n, x, _ in ildizlar)), "noyob_a": sorted(set(round(x, 10) for _, x, _ in ildizlar)),
        "nuqta_soni": nat["nuqta_soni"], "oldi": nat["oldi"], "tirik": nat["tirik"],
        "maks_chuqurlik": nat["maks_chuqurlik"], "chuqurlik_k": nat["maks_chuqurlik"] - 5 * k,
        "shox": nat["shox"], "hammasi_oldi": nat["hammasi_oldi"], "vaqt_s": round(time.time() - t0, 2)}))

if __name__ == "__main__":
    k = int(sys.argv[1]); N = int(sys.argv[2]) if len(sys.argv) > 2 else 5 * k + 60
    main(k, N)
